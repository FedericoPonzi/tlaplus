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
import java.util.List;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import org.junit.Test;

import tlc2.output.EC;
import util.FileUtil;

/**
 * Differential fuzzer: Model-checks random specs (a random state graph whose
 * edges belong to random actions, random fairness, and a random liveness
 * property) with each {@link SccStrategy} and asserts that all strategies
 * agree on the verdict. Unlike UnionFindSccSearchTest, it covers the
 * component checks too, i.e. the tableau, split and deferred checks, and the
 * counterexample reconstruction.
 * <p>
 * Each TLC run is a separate VM because TLC keeps global state. Run longer
 * with -Dtlc2.tool.liveness.SccStrategyFuzzTest.seeds=N and reproduce a
 * failing seed with -D...SccStrategyFuzzTest.seed=S.
 */
public class SccStrategyFuzzTest {

	private static final String PREFIX = SccStrategyFuzzTest.class.getName();
	private static final int SEEDS = Integer.getInteger(PREFIX + ".seeds", 40);
	private static final Integer SEED = Integer.getInteger(PREFIX + ".seed");
	// Absolute, as TLC runs in the spec's temp directory.
	private static final String CLASSPATH = Arrays.stream(System.getProperty("java.class.path").split(File.pathSeparator))
			.map(e -> new File(e).getAbsolutePath()).collect(Collectors.joining(File.pathSeparator));

	@Test
	public void testStrategiesAgreeOnRandomSpecs() throws Exception {
		final int from = SEED != null ? SEED : 0;
		final int to = SEED != null ? SEED + 1 : SEEDS;
		final ExecutorService pool = Executors
				.newFixedThreadPool(Math.max(1, Math.min(4, Runtime.getRuntime().availableProcessors() / 2)));
		try {
			final List<Future<String>> results = new ArrayList<>();
			for (int seed = from; seed < to; seed++) {
				final int s = seed;
				results.add(pool.submit(() -> check(s)));
			}
			int violations = 0;
			for (final Future<String> f : results) {
				if (f.get().equals("violation")) {
					violations++;
				}
			}
			// Guards against a generator whose specs (almost) never or always
			// violate liveness, which would make the comparison weak.
			if (SEED == null) {
				assertTrue("violations=" + violations, violations > 0 && violations < to - from);
			}
		} finally {
			pool.shutdownNow();
		}
	}

	private static String check(final int seed) throws Exception {
		final Random rnd = new Random(seed);
		final Path dir = Files.createTempDirectory("sccfuzz");
		try {
			Files.write(dir.resolve("Fuzz.tla"), spec(rnd).getBytes(StandardCharsets.UTF_8));
			Files.write(dir.resolve("Fuzz.cfg"), "SPECIFICATION Spec\nPROPERTY Prop\n".getBytes(StandardCharsets.UTF_8));
			final String workers = Integer.toString(1 + rnd.nextInt(3));
			final String lncheck = rnd.nextBoolean() ? "final" : "default";
			final String sccWorkers = Integer.toString(1 + rnd.nextInt(4));
			// Small split sizes force split and deferred checks.
			final String splitSize = Integer.toString(new int[] { 1, 3, 1 << 16 }[rnd.nextInt(3)]);

			final int[] exit = new int[SccStrategy.values().length];
			final String[] out = new String[exit.length];
			for (final SccStrategy strategy : SccStrategy.values()) {
				final File log = dir.resolve(strategy + ".out").toFile();
				final Process p = new ProcessBuilder(new File(System.getProperty("java.home"), "bin/java").getPath(),
						"-ea", "-Xmx256m", "-XX:+UseParallelGC", "-cp", CLASSPATH,
						"-D" + SccStrategy.PROPERTY + "=" + strategy,
						"-D" + SccStrategy.WORKERS_PROPERTY + "=" + sccWorkers,
						"-D" + PipelinedComponentChecker.SPLIT_PROPERTY + "=" + splitSize, "tlc2.TLC", "-workers",
						workers, "-lncheck", lncheck, "-deadlock", "-metadir", dir.resolve("states-" + strategy).toString(),
						"Fuzz").directory(dir.toFile()).redirectErrorStream(true).redirectOutput(log).start();
				if (!p.waitFor(5, TimeUnit.MINUTES)) {
					p.destroyForcibly();
				}
				exit[strategy.ordinal()] = p.isAlive() ? -1 : p.exitValue();
				out[strategy.ordinal()] = new String(Files.readAllBytes(log.toPath()), StandardCharsets.UTF_8);
			}
			final String msg = "seed=" + seed + " workers=" + workers + " lncheck=" + lncheck + " sccWorkers="
					+ sccWorkers + " splitSize=" + splitSize + "\n" + Files.readAllLines(dir.resolve("Fuzz.tla"))
					+ "\n" + out[SccStrategy.TARJAN.ordinal()];
			final int expected = exit[SccStrategy.TARJAN.ordinal()];
			assertTrue(msg, expected == EC.ExitStatus.SUCCESS || expected == EC.ExitStatus.VIOLATION_LIVENESS);
			for (final SccStrategy strategy : SccStrategy.values()) {
				assertEquals(strategy + " " + msg + "\n" + out[strategy.ordinal()], expected,
						exit[strategy.ordinal()]);
			}
			return expected == EC.ExitStatus.SUCCESS ? "ok" : "violation";
		} finally {
			FileUtil.deleteDir(dir.toFile(), true);
		}
	}

	/**
	 * A graph over the states x \in 0..n-1 with edges of k actions, often with
	 * a long cycle, which yields a large SCC.
	 */
	static String spec(final Random rnd) {
		final int n = rnd.nextInt(4) == 0 ? 50 + rnd.nextInt(250) : 2 + rnd.nextInt(20);
		final int k = 1 + rnd.nextInt(3);
		final double degree = 0.3 + rnd.nextDouble() * 2;
		final List<List<List<Integer>>> succ = new ArrayList<>();
		for (int a = 0; a < k; a++) {
			final List<List<Integer>> s = new ArrayList<>();
			for (int i = 0; i < n; i++) {
				s.add(new ArrayList<>());
			}
			succ.add(s);
		}
		final int edges = (int) (n * degree);
		for (int e = 0; e < edges; e++) {
			add(succ.get(rnd.nextInt(k)).get(rnd.nextInt(n)), rnd.nextInt(n));
		}
		if (rnd.nextBoolean()) {
			for (int i = 0; i < n; i++) {
				add(succ.get(rnd.nextInt(k)).get(i), (i + 1) % n);
			}
		}

		final StringBuilder sb = new StringBuilder("---- MODULE Fuzz ----\nEXTENDS Naturals\nVARIABLE x\n");
		for (int a = 0; a < k; a++) {
			sb.append("S").append(a).append(" == <<");
			for (int i = 0; i < n; i++) {
				sb.append(i == 0 ? "" : ", ").append(set(succ.get(a).get(i)));
			}
			sb.append(">>\nA").append(a).append(" == x' \\in S").append(a).append("[x + 1]\n");
		}
		final List<Integer> init = new ArrayList<>();
		init.add(0);
		if (rnd.nextInt(3) == 0) {
			add(init, rnd.nextInt(n));
		}
		sb.append("Init == x \\in ").append(set(init)).append('\n');
		sb.append("Next == ");
		for (int a = 0; a < k; a++) {
			sb.append(a == 0 ? "" : " \\/ ").append('A').append(a);
		}
		sb.append("\nSpec == Init /\\ [][Next]_x");
		for (int a = 0; a < k; a++) {
			switch (rnd.nextInt(4)) {
			case 0:
				break;
			case 1:
				sb.append(" /\\ SF_x(A").append(a).append(')');
				break;
			default:
				sb.append(" /\\ WF_x(A").append(a).append(')');
			}
		}
		if (rnd.nextInt(3) == 0) {
			sb.append(" /\\ WF_x(Next)");
		}
		sb.append("\nProp == ").append(property(rnd, n, k));
		if (rnd.nextInt(4) == 0) {
			sb.append(" /\\ ").append(property(rnd, n, k));
		}
		return sb.append("\n====\n").toString();
	}

	private static String property(final Random rnd, final int n, final int k) {
		switch (rnd.nextInt(5)) {
		case 0:
			return "[]<>(x \\in " + subset(rnd, n) + ")";
		case 1:
			return "<>[](x \\in " + subset(rnd, n) + ")";
		case 2:
			return "((x \\in " + subset(rnd, n) + ") ~> (x \\in " + subset(rnd, n) + "))";
		case 3:
			return "[]<><<A" + rnd.nextInt(k) + ">>_x";
		default:
			return "<>[][A" + rnd.nextInt(k) + "]_x";
		}
	}

	private static String subset(final Random rnd, final int n) {
		final List<Integer> s = new ArrayList<>();
		final double p = rnd.nextDouble();
		for (int i = 0; i < n; i++) {
			if (rnd.nextDouble() < p) {
				s.add(i);
			}
		}
		return set(s);
	}

	private static void add(final List<Integer> l, final int i) {
		if (!l.contains(i)) {
			l.add(i);
		}
	}

	private static String set(final List<Integer> l) {
		final StringBuilder sb = new StringBuilder("{");
		for (int i = 0; i < l.size(); i++) {
			sb.append(i == 0 ? "" : ", ").append(l.get(i));
		}
		return sb.append('}').toString();
	}
}
