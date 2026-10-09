/*******************************************************************************
 * Copyright (c) 2026 Microsoft Research. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ******************************************************************************/
package tlc2.tool.liveness;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.LockSupport;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Collectors;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.FileUtil;

/**
 * Trace validation of {@link UnionFindSccSearch} against
 * test-model/scc/UFSCC.tla: Each run on a random graph is logged and TLC
 * checks with UFSCCTrace.tla that the log is a behavior of UFSCC.
 * <p>
 * Run more traces with -Dtlc2.tool.liveness.UnionFindSccSearchTraceTest.traces=N
 * and reproduce one with ...UnionFindSccSearchTraceTest.seed=N (and .keep=true
 * to keep its log).
 */
public class UnionFindSccSearchTraceTest {

	private static final String PREFIX = UnionFindSccSearchTraceTest.class.getName();
	private static final int TRACES = Integer.getInteger(PREFIX + ".traces", 50);
	private static final Integer SEED = Integer.getInteger(PREFIX + ".seed");
	// Keeps the logs of accepted traces too.
	private static final boolean KEEP = Boolean.getBoolean(PREFIX + ".keep");
	private static final String CLASSPATH = Arrays.stream(System.getProperty("java.class.path").split(File.pathSeparator))
			.map(e -> new File(e).getAbsolutePath()).collect(Collectors.joining(File.pathSeparator));
	private static final File SPEC_DIR = new File(CommonTestCase.BASE_DIR, "test-model" + File.separator + "scc")
			.getAbsoluteFile();

	@Test
	public void testTracesAreBehaviorsOfUFSCC() throws Exception {
		final int from = SEED != null ? SEED : 0;
		final int to = SEED != null ? SEED + 1 : TRACES;
		final ExecutorService search = Executors.newFixedThreadPool(8);
		final ExecutorService tlc = Executors
				.newFixedThreadPool(Math.max(1, Math.min(4, Runtime.getRuntime().availableProcessors() / 2)));
		try {
			final List<Future<String>> results = new ArrayList<>();
			for (int seed = from; seed < to; seed++) {
				final Path trace = run(seed, search);
				final int s = seed;
				results.add(tlc.submit(() -> validate(s, trace)));
			}
			int violations = 0;
			for (final Future<String> f : results) {
				if (f.get().equals("violation")) {
					violations++;
				}
			}
			if (SEED == null) {
				assertTrue("violations=" + violations, violations > 0 && violations < to - from);
			}
		} finally {
			search.shutdownNow();
			tlc.shutdownNow();
		}
	}

	/**
	 * @return The log of a search of a random graph.
	 */
	private static Path run(final int seed, final ExecutorService pool) throws Exception {
		final Random rnd = new Random(seed);
		final int n = 5 + rnd.nextInt(26);
		final int workers = 1 + rnd.nextInt(4);
		final UnionFindSccSearchTest.Graph g = dedupe(UnionFindSccSearchTest.Graph.random(rnd, n,
				0.5 + rnd.nextDouble() * 2, rnd.nextBoolean() ? 0 : 0.15, 1 + rnd.nextInt(3)));
		final int bad = rnd.nextBoolean() ? rnd.nextInt(n) : -1;

		final StepTracer tracer = new StepTracer(seed);
		final UnionFindSccSearch search = new UnionFindSccSearch(workers, UnionFindSccSearchTest.successorsOf(g),
				(root, size) -> {
					final List<UnionFindSccSearch.Node> members = UnionFindSccSearch.members(root);
					assertEquals(size, members.size());
					// The check event logs what the listener received.
					tracer.found = root;
					return members.stream().anyMatch(m -> m.fp == bad);
				});
		search.setTracer(tracer);
		for (final int i : g.inits) {
			search.addRoot(search.node(i, 0, i));
		}
		search.run(pool);

		final StringJoiner edges = new StringJoiner(",", "[", "]");
		for (int u = 0; u < n; u++) {
			for (final int v : g.succ.get(u)) {
				if (!g.isPruned(u, v)) {
					edges.add("[" + u + "," + v + "]");
				}
			}
		}
		final StringBuilder log = new StringBuilder();
		log.append("{\"nodes\":").append(n).append(",\"workers\":").append(workers).append(",\"edges\":")
				.append(edges).append(",\"roots\":").append(tracer.roots).append(",\"bad\":")
				.append(bad < 0 ? "[]" : "[" + bad + "]").append("}\n");
		for (final String e : tracer.events) {
			log.append(e).append('\n');
		}
		final Path file = Files.createTempFile("ufscc-trace-" + seed + "-", ".ndjson");
		Files.write(file, log.toString().getBytes(StandardCharsets.UTF_8));
		return file;
	}

	private static String validate(final int seed, final Path trace) throws Exception {
		final Path dir = Files.createTempDirectory("ufscctrace");
		boolean ok = false;
		try {
			final String cfg = new String(Files.readAllBytes(new File(SPEC_DIR, "UFSCCTrace.cfg").toPath()),
					StandardCharsets.UTF_8).replace("TRACE_FILE", trace.toString().replace("\\", "\\\\"));
			final Path cfgFile = dir.resolve("UFSCCTrace.cfg");
			Files.write(cfgFile, cfg.getBytes(StandardCharsets.UTF_8));
			final File out = dir.resolve("tlc.out").toFile();
			final Process p = new ProcessBuilder(new File(System.getProperty("java.home"), "bin/java").getPath(),
					"-Xmx512m", "-XX:+UseParallelGC", "-cp", CLASSPATH, "tlc2.TLC", "-noGenerateSpecTE", "-workers", "1", "-metadir",
					dir.resolve("states").toString(), "-config", cfgFile.toString(),
					new File(SPEC_DIR, "UFSCCTrace.tla").getPath()).directory(dir.toFile()).redirectErrorStream(true)
					.redirectOutput(out).start();
			if (!p.waitFor(5, TimeUnit.MINUTES)) {
				p.destroyForcibly();
			}
			final String output = new String(Files.readAllBytes(out.toPath()), StandardCharsets.UTF_8);
			ok = !p.isAlive() && p.exitValue() == 0 && output.contains("No error has been found");
			assertTrue("seed=" + seed + " trace=" + trace + "\n" + output, ok);
			return Files.readAllLines(trace).stream().anyMatch(l -> l.contains("\"bad\":true")) ? "violation" : "ok";
		} finally {
			FileUtil.deleteDir(dir.toFile(), true);
			if (ok && !KEEP) {
				Files.deleteIfExists(trace);
			}
		}
	}

	/**
	 * UFSCC's successors of a node are a set.
	 */
	private static UnionFindSccSearchTest.Graph dedupe(final UnionFindSccSearchTest.Graph g) {
		final UnionFindSccSearchTest.Graph d = new UnionFindSccSearchTest.Graph(g.n);
		for (int u = 0; u < g.n; u++) {
			for (final int v : new LinkedHashSet<>(g.succ.get(u))) {
				d.edge(u, v, g.isPruned(u, v));
			}
		}
		d.inits.addAll(g.inits);
		return d;
	}

	/**
	 * Lets one worker at a time run from one yield to the next, so that the
	 * logged steps are atomic and logged in the order they happen. Random
	 * pauses at the yields vary the interleavings.
	 */
	private static final class StepTracer implements UnionFindSccSearch.Tracer {
		private final ReentrantLock lock = new ReentrantLock();
		private final Random rnd;
		final List<String> events = new ArrayList<>();
		final Set<Long> rootSet = new LinkedHashSet<>();
		final StringJoiner roots = new StringJoiner(",", "[", "]");
		// The root passed to the listener by the last report.
		UnionFindSccSearch.Node found;

		StepTracer(final int seed) {
			this.rnd = new Random(seed);
		}

		@Override
		public void enter(final int worker) {
			lock.lock();
		}

		@Override
		public void yieldStep(final int worker) {
			final int pause;
			synchronized (rnd) {
				pause = rnd.nextInt(4);
			}
			lock.unlock();
			if (pause == 1) {
				Thread.yield();
			} else if (pause == 2) {
				LockSupport.parkNanos(20_000);
			}
			lock.lock();
		}

		@Override
		public void exit(final int worker) {
			if (lock.isHeldByCurrentThread()) {
				lock.unlock();
			}
		}

		@Override
		public void addedRoot(final UnionFindSccSearch.Node n) {
			// Initial nodes are added before the workers start.
			synchronized (rootSet) {
				if (rootSet.add(n.fp)) {
					roots.add(Long.toString(n.fp));
				}
			}
		}

		@Override
		public void event(final int worker, final String action, final Object... args) {
			final StringBuilder sb = new StringBuilder("{\"p\":").append(worker).append(",\"a\":\"").append(action)
					.append('"');
			switch (action) {
			case "start":
			case "claim":
				sb.append(",\"n\":").append(((UnionFindSccSearch.Node) args[0]).fp).append(",\"r\":\"")
						.append(args[1]).append('"');
				break;
			case "merge":
				sb.append(",\"root\":").append(((UnionFindSccSearch.Node) args[0]).fp).append(",\"child\":")
						.append(((UnionFindSccSearch.Node) args[1]).fp);
				break;
			case "fetch":
				sb.append(",\"n\":").append(((UnionFindSccSearch.Node) args[0]).fp);
				break;
			case "remove":
			case "pick":
				sb.append(",\"s\":").append(ids(Arrays.asList((UnionFindSccSearch.Node[]) args[0])));
				break;
			case "complete":
				sb.append(",\"r\":").append(((UnionFindSccSearch.Node) args[0]).fp);
				break;
			case "check":
				final UnionFindSccSearch.Node r = found;
				sb.append(",\"r\":").append(r.fp).append(",\"s\":").append(ids(UnionFindSccSearch.members(r)))
						.append(",\"bad\":").append(args[1]);
				break;
			default:
				break;
			}
			events.add(sb.append('}').toString());
		}

		private static String ids(final List<UnionFindSccSearch.Node> ns) {
			return ns.stream().map(x -> Long.toString(x.fp)).collect(Collectors.joining(",", "[", "]"));
		}
	}
}
