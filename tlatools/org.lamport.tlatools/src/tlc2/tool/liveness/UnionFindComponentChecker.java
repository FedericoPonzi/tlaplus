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

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import tlc2.util.LongVec;

/**
 * {@link SccStrategy#UFSCC}: Searches the SCCs of a liveness graph (for one
 * PEM) with {@link UnionFindSccSearch} and checks each SCC in the thread that
 * completes it. Like LiveWorker#checkSccs, the search follows only the edges
 * that satisfy the PEM's EAAction.
 */
final class UnionFindComponentChecker {

	// For tests to assert UFSCC was used.
	static final AtomicLong SEARCHES = new AtomicLong();
	static final AtomicLong SPLITS = new AtomicLong();

	/** An SCC that violates liveness, for LiveWorker#printTrace. */
	static final class CounterExample {
		final long state;
		final int tidx;
		final TableauNodePtrTable com;

		private CounterExample(final long state, final int tidx, final TableauNodePtrTable com) {
			this.state = state;
			this.tidx = tidx;
			this.com = com;
		}
	}

	private final AbstractDiskGraph dg;
	private final ComponentChecker checker;
	private final int[] eaaction;
	private final int slen;
	private final int alen;
	private final boolean isFinalCheck;
	private final int splitSize;
	private final NodeReaders readers;
	// Checking a large SCC in the worker that completes it would serialize the
	// check, thus all workers check them once the search is done.
	private final Queue<UnionFindSccSearch.Node> deferred = new ConcurrentLinkedQueue<>();
	private final AtomicReference<TableauNodePtrTable> bad = new AtomicReference<>();

	private UnionFindComponentChecker(final AbstractDiskGraph dg, final ComponentChecker checker,
			final OrderOfSolution oos, final PossibleErrorModel pem, final boolean isFinalCheck) {
		this.dg = dg;
		this.checker = checker;
		this.eaaction = pem.EAAction;
		this.slen = oos.getCheckState().length;
		this.alen = oos.getCheckAction().length;
		this.isFinalCheck = isFinalCheck;
		this.splitSize = PipelinedComponentChecker.splitSize();
		this.readers = new NodeReaders(dg);
	}

	/**
	 * @return An SCC that violates liveness or null if there is none.
	 */
	static CounterExample check(final ExecutorService pool, final int workers, final AbstractDiskGraph dg,
			final ComponentChecker checker, final OrderOfSolution oos, final PossibleErrorModel pem,
			final boolean isFinalCheck) throws IOException, InterruptedException {
		SEARCHES.incrementAndGet();
		return new UnionFindComponentChecker(dg, checker, oos, pem, isFinalCheck).check(pool, workers);
	}

	private CounterExample check(final ExecutorService pool, final int workers)
			throws IOException, InterruptedException {
		// The search never assigns links, thus getLink returns the nodes' file
		// pointers, which identify the nodes.
		this.dg.makeNodePtrTblIfStale();
		this.dg.prepareForReads();

		final int expectedNodes = (int) Math.min(this.dg.size(), Integer.MAX_VALUE / 2);
		final UnionFindSccSearch search = new UnionFindSccSearch(workers, expectedNodes, this::successors,
				this::violates);
		final LongVec initNodes = this.dg.getInitNodes();
		for (int j = 0; j < initNodes.size(); j += 2) {
			final long state = initNodes.elementAt(j);
			final int tidx = (int) initNodes.elementAt(j + 1);
			final long ptr = this.dg.getLink(state, tidx);
			// Same as LiveWorker#checkSccs.
			if (ptr >= 0) {
				search.addRoot(search.node(state, tidx, ptr));
			} else {
				assert !this.isFinalCheck || (ptr != TableauNodePtrTable.UNDONE && ptr != TableauNodePtrTable.DONE);
			}
		}
		try {
			search.run(pool);
		} catch (UncheckedIOException e) {
			throw e.getCause();
		} finally {
			this.readers.close();
		}
		TableauNodePtrTable com = this.bad.get();
		if (com == null && !this.deferred.isEmpty()) {
			final UnionFindSccSearch.Node root = checkDeferred(pool, workers, search);
			if (root != null) {
				com = toTable(UnionFindSccSearch.members(root));
			}
		}
		return com == null ? null : entry(com);
	}

	/**
	 * Checks the deferred SCCs in a single pass of all workers over the nodes,
	 * which unlike building an SCC's {@link TableauNodePtrTable} first, is not
	 * serial.
	 * 
	 * @return The root of a deferred SCC that violates liveness or null.
	 */
	private UnionFindSccSearch.Node checkDeferred(final ExecutorService pool, final int workers,
			final UnionFindSccSearch search) throws IOException, InterruptedException {
		final List<UnionFindSccSearch.Node> roots = new ArrayList<>(this.deferred);
		SPLITS.addAndGet(roots.size());
		final Map<UnionFindSccSearch.Node, Integer> index = new IdentityHashMap<>();
		final ComponentChecker.Members[] members = new ComponentChecker.Members[roots.size()];
		for (int i = 0; i < roots.size(); i++) {
			final UnionFindSccSearch.Node root = roots.get(i);
			index.put(root, i);
			members[i] = (fp, tidx) -> {
				final UnionFindSccSearch.Node n = search.get(fp, tidx);
				return n != null && UnionFindSccSearch.root(n) == root;
			};
		}
		// Sorted by ptr, a chunk's reads are sequential and mostly served by the
		// reader's buffer instead of each costing a syscall.
		final List<Callable<List<UnionFindSccSearch.Node>>> collect = new ArrayList<>(workers);
		for (int c = 0; c < workers; c++) {
			final int chunk = c;
			collect.add(() -> {
				final List<UnionFindSccSearch.Node> nodes = new ArrayList<>();
				search.forEachNode(chunk, workers, n -> {
					if (index.containsKey(UnionFindSccSearch.root(n))) {
						nodes.add(n);
					}
				});
				return nodes;
			});
		}
		final List<UnionFindSccSearch.Node> all = new ArrayList<>();
		for (final Future<List<UnionFindSccSearch.Node>> f : pool.invokeAll(collect)) {
			all.addAll(PipelinedComponentChecker.get(f));
		}
		final UnionFindSccSearch.Node[] nodes = all.toArray(new UnionFindSccSearch.Node[all.size()]);
		all.clear();
		Arrays.parallelSort(nodes, Comparator.comparingLong(n -> n.ptr));

		final List<Callable<ComponentChecker.Result[]>> chunks = new ArrayList<>(workers);
		for (int c = 0; c < workers; c++) {
			final int from = (int) ((long) nodes.length * c / workers);
			final int to = (int) ((long) nodes.length * (c + 1) / workers);
			chunks.add(() -> {
				final ComponentChecker.Result[] res = new ComponentChecker.Result[roots.size()];
				for (int i = 0; i < res.length; i++) {
					res[i] = this.checker.newResult();
				}
				// Not this.readers: a chunk may outlive an interrupted invokeAll.
				try (AbstractDiskGraph.NodeReader reader = this.dg.newNodeReader()) {
					for (int j = from; j < to; j++) {
						final UnionFindSccSearch.Node n = nodes[j];
						final int i = index.get(UnionFindSccSearch.root(n));
						this.checker.check(reader.read(n.fp, n.tidx, n.ptr), members[i], res[i]);
					}
				}
				return res;
			});
		}
		final ComponentChecker.Result[] res = new ComponentChecker.Result[roots.size()];
		for (int i = 0; i < res.length; i++) {
			res[i] = this.checker.newResult();
		}
		for (final Future<ComponentChecker.Result[]> f : pool.invokeAll(chunks)) {
			final ComponentChecker.Result[] r = PipelinedComponentChecker.get(f);
			for (int i = 0; i < res.length; i++) {
				res[i].or(r[i]);
			}
		}
		for (int i = 0; i < res.length; i++) {
			if (res[i].isCounterExample()) {
				return roots.get(i);
			}
		}
		return null;
	}

	private static TableauNodePtrTable toTable(final List<UnionFindSccSearch.Node> scc) {
		final TableauNodePtrTable com = new TableauNodePtrTable(Math.max(128, 2 * scc.size()));
		for (final UnionFindSccSearch.Node n : scc) {
			com.put(n.fp, n.tidx, n.ptr);
		}
		com.prepareForReads();
		return com;
	}

	/**
	 * printTrace recreates the cycle starting at the returned node. Unlike an
	 * arbitrary node of com, the node at which a shortest path from an initial
	 * node enters com is where the counterexample of a trace spec, whose
	 * next-state relation depends on TLCGet("level"), starts (Github issue #1045).
	 */
	private CounterExample entry(final TableauNodePtrTable com) throws IOException {
		final TableauNodePtrTable seen = new TableauNodePtrTable(1024);
		final ArrayDeque<long[]> queue = new ArrayDeque<>();
		final LongVec initNodes = this.dg.getInitNodes();
		for (int j = 0; j < initNodes.size(); j += 2) {
			final long state = initNodes.elementAt(j);
			final int tidx = (int) initNodes.elementAt(j + 1);
			if (com.get(state, tidx) != -1) {
				return new CounterExample(state, tidx, com);
			}
			enqueue(seen, queue, state, tidx);
		}
		while (!queue.isEmpty()) {
			final long[] cur = queue.poll();
			final GraphNode gnode = this.dg.getNode(cur[0], (int) cur[1], cur[2]);
			for (int i = 0; i < gnode.succSize(); i++) {
				final long state = gnode.getStateFP(i);
				final int tidx = gnode.getTidx(i);
				if (com.get(state, tidx) != -1) {
					return new CounterExample(state, tidx, com);
				}
				enqueue(seen, queue, state, tidx);
			}
		}
		throw new IllegalStateException("SCC unreachable from the initial nodes");
	}

	private void enqueue(final TableauNodePtrTable seen, final ArrayDeque<long[]> queue, final long state,
			final int tidx) {
		final long ptr = this.dg.getLink(state, tidx);
		if (ptr >= 0 && seen.get(state, tidx) == -1) {
			seen.put(state, tidx, ptr);
			queue.add(new long[] { state, tidx, ptr });
		}
	}

	private UnionFindSccSearch.Node[] successors(final UnionFindSccSearch.Node node,
			final UnionFindSccSearch search) throws IOException {
		final GraphNode gnode = this.readers.get().read(node.fp, node.tidx, node.ptr);
		final int succCnt = gnode.succSize();
		final List<UnionFindSccSearch.Node> succs = new ArrayList<>(succCnt);
		for (int i = 0; i < succCnt; i++) {
			final long nextState = gnode.getStateFP(i);
			final int nextTidx = gnode.getTidx(i);
			// Cheaper than getLink, which dominated the search's profile.
			UnionFindSccSearch.Node next = search.get(nextState, nextTidx);
			if (next == null) {
				final long nextLink = this.dg.getLink(nextState, nextTidx);
			// Same as LiveWorker#checkSccs.
				if (nextLink < 0) {
					assert !this.isFinalCheck || nextLink != TableauNodePtrTable.UNDONE;
					continue;
				}
				next = search.node(nextState, nextTidx, nextLink);
			}
			if (gnode.getCheckAction(this.slen, this.alen, i, this.eaaction)) {
				succs.add(next);
			} else {
				search.addRoot(next);
			}
		}
		return succs.toArray(new UnionFindSccSearch.Node[succs.size()]);
	}

	/**
	 * @return true iff scc violates liveness (which stops the search).
	 */
	private boolean violates(final UnionFindSccSearch.Node root, final int size) throws IOException {
		final AbstractDiskGraph.NodeReader reader = this.readers.get();
		// Same as LiveWorker#checkComponent: A single node is trivial unless it
		// stutters.
		if (size == 1 && !this.checker.isStuttering(reader.read(root.fp, root.tidx, root.ptr))) {
			return false;
		}
		if (size >= this.splitSize) {
			this.deferred.add(root);
			return false;
		}
		final TableauNodePtrTable com = toTable(UnionFindSccSearch.members(root));
		if (!this.checker.isCounterExample(com, reader::read)) {
			return false;
		}
		this.bad.compareAndSet(null, com);
		return true;
	}
}
