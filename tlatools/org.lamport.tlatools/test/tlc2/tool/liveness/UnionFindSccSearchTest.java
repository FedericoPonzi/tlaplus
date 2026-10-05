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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

public class UnionFindSccSearchTest {

	private static ExecutorService pool;

	@BeforeClass
	public static void beforeClass() {
		pool = Executors.newFixedThreadPool(8);
	}

	@AfterClass
	public static void afterClass() {
		pool.shutdownNow();
	}

	/**
	 * A directed graph over the nodes 0..n-1. Pruned edges are not followed by
	 * the SCC search; their targets become new roots instead (like edges that
	 * violate a PEM's EAAction in LiveWorker).
	 */
	private static final class Graph {
		final int n;
		final List<List<Integer>> succ = new ArrayList<>();
		final Set<Long> pruned = new HashSet<>();
		final List<Integer> inits = new ArrayList<>();

		Graph(final int n) {
			this.n = n;
			for (int i = 0; i < n; i++) {
				succ.add(new ArrayList<>());
			}
		}

		void edge(final int from, final int to, final boolean isPruned) {
			succ.get(from).add(to);
			if (isPruned) {
				pruned.add((long) from * n + to);
			}
		}

		boolean isPruned(final int from, final int to) {
			return pruned.contains((long) from * n + to);
		}

		static Graph random(final Random rnd, final int n, final double avgDegree, final double prunedProb,
				final int numInits) {
			final Graph g = new Graph(n);
			for (int u = 0; u < n; u++) {
				final int deg = (int) Math.round(rnd.nextDouble() * 2 * avgDegree);
				for (int k = 0; k < deg; k++) {
					g.edge(u, rnd.nextInt(n), rnd.nextDouble() < prunedProb);
				}
			}
			for (int i = 0; i < numInits; i++) {
				g.inits.add(rnd.nextInt(n));
			}
			return g;
		}

		/** Tarjan's SCCs over the followed edges of the nodes reachable via any edge. */
		Set<Set<Integer>> referenceSccs() {
			final BitSet reachable = new BitSet(n);
			final ArrayDeque<Integer> todo = new ArrayDeque<>(inits);
			while (!todo.isEmpty()) {
				final int u = todo.pop();
				if (!reachable.get(u)) {
					reachable.set(u);
					todo.addAll(succ.get(u));
				}
			}
			final int[] index = new int[n];
			final int[] low = new int[n];
			Arrays.fill(index, -1);
			final boolean[] onStack = new boolean[n];
			final ArrayDeque<Integer> stack = new ArrayDeque<>();
			final Set<Set<Integer>> result = new HashSet<>();
			int counter = 0;
			for (int s = reachable.nextSetBit(0); s >= 0; s = reachable.nextSetBit(s + 1)) {
				if (index[s] != -1) {
					continue;
				}
				// Iterative Tarjan: frames of <node, next successor index>.
				final ArrayDeque<int[]> frames = new ArrayDeque<>();
				frames.push(new int[] { s, 0 });
				index[s] = low[s] = counter++;
				stack.push(s);
				onStack[s] = true;
				while (!frames.isEmpty()) {
					final int[] f = frames.peek();
					final int u = f[0];
					final List<Integer> out = succ.get(u);
					if (f[1] < out.size()) {
						final int v = out.get(f[1]++);
						if (isPruned(u, v)) {
							continue;
						}
						if (index[v] == -1) {
							index[v] = low[v] = counter++;
							stack.push(v);
							onStack[v] = true;
							frames.push(new int[] { v, 0 });
						} else if (onStack[v]) {
							low[u] = Math.min(low[u], index[v]);
						}
						continue;
					}
					frames.pop();
					if (!frames.isEmpty()) {
						low[frames.peek()[0]] = Math.min(low[frames.peek()[0]], low[u]);
					}
					if (low[u] == index[u]) {
						final Set<Integer> scc = new HashSet<>();
						int v;
						do {
							v = stack.pop();
							onStack[v] = false;
							scc.add(v);
						} while (v != u);
						result.add(scc);
					}
				}
			}
			return result;
		}
	}

	private static final class Recorder implements UnionFindSccSearch.SccListener {
		final List<Set<Integer>> sccs = Collections.synchronizedList(new ArrayList<>());

		@Override
		public boolean found(final UnionFindSccSearch.Node root, final int size) {
			final List<UnionFindSccSearch.Node> scc = UnionFindSccSearch.members(root);
			assertEquals(size, scc.size());
			final Set<Integer> s = new HashSet<>();
			for (final UnionFindSccSearch.Node n : scc) {
				assertSame(root, UnionFindSccSearch.root(n));
				assertTrue("Node reported twice within an SCC", s.add((int) n.fp));
			}
			sccs.add(s);
			return false;
		}
	}

	private static UnionFindSccSearch.Successors successorsOf(final Graph g) {
		return (node, search) -> {
			final int u = (int) node.fp;
			final List<UnionFindSccSearch.Node> out = new ArrayList<>();
			for (final int v : g.succ.get(u)) {
				final UnionFindSccSearch.Node w = search.node(v, 0, v);
				if (g.isPruned(u, v)) {
					search.addRoot(w);
				} else {
					out.add(w);
				}
			}
			return out.toArray(new UnionFindSccSearch.Node[0]);
		};
	}

	private static List<Set<Integer>> search(final Graph g, final int workers) throws Exception {
		final Recorder rec = new Recorder();
		final UnionFindSccSearch search = new UnionFindSccSearch(workers, successorsOf(g), rec);
		for (final int i : g.inits) {
			search.addRoot(search.node(i, 0, i));
		}
		search.run(pool);
		return rec.sccs;
	}

	private static void assertSameSccs(final Graph g, final List<Set<Integer>> actual, final String msg) {
		final Set<Integer> seen = new HashSet<>();
		for (final Set<Integer> scc : actual) {
			for (final int v : scc) {
				assertTrue(msg + ": node " + v + " reported in more than one SCC", seen.add(v));
			}
		}
		assertEquals(msg, g.referenceSccs(), new HashSet<>(actual));
	}

	@Test
	public void testRandomGraphsMatchTarjan() throws Exception {
		for (final int workers : new int[] { 1, 2, 4, 8 }) {
			for (int seed = 0; seed < 300; seed++) {
				final Random rnd = new Random(seed);
				final Graph g = Graph.random(rnd, 1 + rnd.nextInt(60), 0.5 + rnd.nextDouble() * 3,
						rnd.nextDouble() * 0.3, 1 + rnd.nextInt(3));
				assertSameSccs(g, search(g, workers), "workers=" + workers + " seed=" + seed);
			}
		}
	}

	@Test
	public void testLargeRandomGraphsMatchTarjan() throws Exception {
		for (int seed = 0; seed < 10; seed++) {
			final Random rnd = new Random(seed);
			final Graph g = Graph.random(rnd, 20_000, 1.2, seed % 2 == 0 ? 0 : 0.05, 4);
			assertSameSccs(g, search(g, 8), "seed=" + seed);
		}
	}

	@Test
	public void testDenseGraphsMatchTarjan() throws Exception {
		for (int seed = 0; seed < 50; seed++) {
			final Random rnd = new Random(seed);
			final Graph g = Graph.random(rnd, 200, 8, 0, 1);
			assertSameSccs(g, search(g, 8), "seed=" + seed);
		}
	}

	@Test
	public void testLongChainDoesNotOverflowTheStack() throws Exception {
		final int n = 200_000;
		final Graph g = new Graph(n);
		for (int i = 0; i + 1 < n; i++) {
			g.edge(i, i + 1, false);
		}
		g.inits.add(0);
		final List<Set<Integer>> sccs = search(g, 4);
		assertEquals(n, sccs.size());
		assertSameSccs(g, sccs, "chain");
	}

	@Test
	public void testLongCycleIsOneScc() throws Exception {
		final int n = 200_000;
		final Graph g = new Graph(n);
		for (int i = 0; i < n; i++) {
			g.edge(i, (i + 1) % n, false);
		}
		g.inits.add(0);
		final List<Set<Integer>> sccs = search(g, 4);
		assertEquals(1, sccs.size());
		assertEquals(n, sccs.get(0).size());
	}

	@Test
	public void testPrunedEdgeTargetsAreSearched() throws Exception {
		// 0 <-> 1 -pruned-> 2 <-> 3; 1 -pruned-> 0 does not break the 0,1 cycle
		// because 0 -> 1 -> 0 is also followed.
		final Graph g = new Graph(4);
		g.edge(0, 1, false);
		g.edge(1, 0, false);
		g.edge(1, 2, true);
		g.edge(2, 3, false);
		g.edge(3, 2, false);
		g.inits.add(0);
		for (final int workers : new int[] { 1, 4 }) {
			assertSameSccs(g, search(g, workers), "workers=" + workers);
		}
	}

	@Test
	public void testNoInitsNoSccs() throws Exception {
		final Graph g = new Graph(3);
		g.edge(0, 1, false);
		assertEquals(0, search(g, 4).size());
	}

	@Test
	public void testMoreWorkersThanSupportedAreCapped() throws Exception {
		final Random rnd = new Random(42);
		final Graph g = Graph.random(rnd, 500, 2, 0.1, 2);
		assertSameSccs(g, search(g, 1000), "workers=1000");
	}

	@Test
	public void testListenerStopsTheSearch() throws Exception {
		// Many disjoint 2-cycles hanging off a hub.
		final int cycles = 10_000;
		final Graph g = new Graph(1 + 2 * cycles);
		for (int c = 0; c < cycles; c++) {
			final int a = 1 + 2 * c;
			g.edge(0, a, false);
			g.edge(a, a + 1, false);
			g.edge(a + 1, a, false);
		}
		g.inits.add(0);
		final AtomicInteger calls = new AtomicInteger();
		final UnionFindSccSearch search = new UnionFindSccSearch(4, successorsOf(g), (root, size) -> {
			calls.incrementAndGet();
			return size > 1;
		});
		search.addRoot(search.node(0, 0, 0));
		search.run(pool);
		assertTrue(search.isStopped());
		// At most one non-trivial SCC per worker could be reported before
		// the others observe the stop.
		assertTrue("calls=" + calls.get(), calls.get() <= 4);
	}

	@Test
	public void testIOExceptionPropagatesAndWorkersAreDone() throws Exception {
		final Random rnd = new Random(7);
		final Graph g = Graph.random(rnd, 5_000, 2, 0, 1);
		final AtomicInteger active = new AtomicInteger();
		final UnionFindSccSearch.Successors base = successorsOf(g);
		final UnionFindSccSearch search = new UnionFindSccSearch(4, (node, s) -> {
			active.incrementAndGet();
			try {
				if (node.fp == g.succ.size() / 2) {
					throw new IOException("boom");
				}
				return base.of(node, s);
			} finally {
				active.decrementAndGet();
			}
		}, (root, size) -> false);
		for (int v = 0; v < g.n; v++) {
			search.addRoot(search.node(v, 0, v));
		}
		try {
			search.run(pool);
			fail("Expected IOException");
		} catch (IOException e) {
			assertEquals("boom", e.getMessage());
		}
		assertEquals("A worker still runs after run() returned", 0, active.get());
	}

	@Test
	public void testRuntimeExceptionOfListenerPropagates() throws Exception {
		final Graph g = new Graph(2);
		g.edge(0, 1, false);
		g.edge(1, 0, false);
		g.inits.add(0);
		final UnionFindSccSearch search = new UnionFindSccSearch(2, successorsOf(g), (root, size) -> {
			throw new IllegalStateException("listener");
		});
		search.addRoot(search.node(0, 0, 0));
		try {
			search.run(pool);
			fail("Expected IllegalStateException");
		} catch (IllegalStateException e) {
			assertEquals("listener", e.getMessage());
		}
	}

	// The node table starts small (16) and has to grow while the workers
	// concurrently look up and create nodes.
	@Test
	public void testNodeIsUniquePerFpAndTidxConcurrently() throws Exception {
		final UnionFindSccSearch search = new UnionFindSccSearch(1, (node, s) -> new UnionFindSccSearch.Node[0],
				(root, size) -> false);
		// Prime, thus each thread's stride visits every ptr.
		final int n = 100_003;
		final int threads = 8;
		final UnionFindSccSearch.Node[][] seen = new UnionFindSccSearch.Node[threads][n];
		final List<Future<?>> futures = new ArrayList<>();
		for (int t = 0; t < threads; t++) {
			final int tt = t;
			futures.add(pool.submit(() -> {
				for (int k = 0; k < n; k++) {
					// Each thread visits the ptrs in a different order.
					final int i = (int) ((k * (2L * tt + 1)) % n);
					// Nodes of the same fp differ in tidx.
					seen[tt][i] = search.node(i / 3, i % 3, i * 37L);
				}
			}));
		}
		for (final Future<?> f : futures) {
			f.get();
		}
		for (int i = 0; i < n; i++) {
			assertEquals(i * 37L, seen[0][i].ptr);
			for (int t = 1; t < threads; t++) {
				assertSame(seen[0][i], seen[t][i]);
			}
			assertSame(seen[0][i], search.get(i / 3, i % 3));
		}
		assertNull(search.get(0L, 3));
		assertNull(search.get(n, 0));

		final Set<Long> scanned = Collections.synchronizedSet(new HashSet<>());
		final int chunks = 3;
		for (int c = 0; c < chunks; c++) {
			search.forEachNode(c, chunks, node -> assertTrue(scanned.add(node.ptr)));
		}
		assertEquals(n, scanned.size());
	}

	@Test
	public void testRunsWithoutPool() throws Exception {
		final Random rnd = new Random(3);
		final Graph g = Graph.random(rnd, 300, 2, 0.1, 2);
		final Recorder rec = new Recorder();
		final UnionFindSccSearch search = new UnionFindSccSearch(1, successorsOf(g), rec);
		for (final int i : g.inits) {
			search.addRoot(search.node(i, 0, i));
		}
		search.run(null);
		assertSameSccs(g, rec.sccs, "no pool");
	}
}
