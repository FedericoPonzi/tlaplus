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
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
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
	private final Map<Thread, AbstractDiskGraph.NodeReader> readers = new ConcurrentHashMap<>();
	// Checking a large SCC in the worker that completes it would serialize the
	// check, thus all workers check them once the search is done.
	private final Queue<TableauNodePtrTable> deferred = new ConcurrentLinkedQueue<>();
	private final AtomicReference<TableauNodePtrTable> bad = new AtomicReference<>();

	private UnionFindComponentChecker(final AbstractDiskGraph dg, final ComponentChecker checker,
			final OrderOfSolution oos, final PossibleErrorModel pem, final boolean isFinalCheck) {
		this.dg = dg;
		this.checker = checker;
		this.eaaction = pem.EAAction;
		this.slen = oos.getCheckState().length;
		this.alen = oos.getCheckAction().length;
		this.isFinalCheck = isFinalCheck;
		this.splitSize = Math.max(1, Integer.getInteger(PipelinedComponentChecker.SPLIT_PROPERTY, 1 << 16));
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
		this.dg.makeNodePtrTbl();
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
			closeReaders();
		}
		TableauNodePtrTable com = this.bad.get();
		for (final TableauNodePtrTable d : this.deferred) {
			if (com != null) {
				break;
			}
			if (checkSplit(pool, workers, d)) {
				com = d;
			}
		}
		return com == null ? null : entry(com);
	}

	private boolean checkSplit(final ExecutorService pool, final int workers, final TableauNodePtrTable com)
			throws IOException, InterruptedException {
		SPLITS.incrementAndGet();
		final int size = com.getSize();
		final List<Callable<ComponentChecker.Result>> chunks = new ArrayList<>(workers);
		for (int i = 0; i < workers; i++) {
			final int from = (int) ((long) size * i / workers);
			final int to = (int) ((long) size * (i + 1) / workers);
			chunks.add(() -> {
				// Not reader(): a chunk may outlive an interrupted invokeAll.
				try (AbstractDiskGraph.NodeReader reader = this.dg.newNodeReader()) {
					final ComponentChecker.Result res = this.checker.newResult();
					this.checker.check(com, from, to, reader::read, res);
					return res;
				}
			});
		}
		final ComponentChecker.Result res = this.checker.newResult();
		for (final Future<ComponentChecker.Result> f : pool.invokeAll(chunks)) {
			res.or(PipelinedComponentChecker.get(f));
		}
		return res.isCounterExample();
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
		final GraphNode gnode = reader().read(node.fp, node.tidx, node.ptr);
		final int succCnt = gnode.succSize();
		final List<UnionFindSccSearch.Node> succs = new ArrayList<>(succCnt);
		for (int i = 0; i < succCnt; i++) {
			final long nextState = gnode.getStateFP(i);
			final int nextTidx = gnode.getTidx(i);
			final long nextLink = this.dg.getLink(nextState, nextTidx);
			// Same as LiveWorker#checkSccs.
			if (nextLink < 0) {
				assert !this.isFinalCheck || nextLink != TableauNodePtrTable.UNDONE;
				continue;
			}
			final UnionFindSccSearch.Node next = search.node(nextState, nextTidx, nextLink);
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
	private boolean violates(final List<UnionFindSccSearch.Node> scc) throws IOException {
		final AbstractDiskGraph.NodeReader reader = reader();
		final UnionFindSccSearch.Node first = scc.get(0);
		// Same as LiveWorker#checkComponent: A single node is trivial unless it
		// stutters.
		if (scc.size() == 1 && !this.checker.isStuttering(reader.read(first.fp, first.tidx, first.ptr))) {
			return false;
		}
		final TableauNodePtrTable com = new TableauNodePtrTable(Math.max(128, 2 * scc.size()));
		for (final UnionFindSccSearch.Node n : scc) {
			com.put(n.fp, n.tidx, n.ptr);
		}
		com.prepareForReads();
		if (scc.size() >= this.splitSize) {
			this.deferred.add(com);
			return false;
		}
		final ComponentChecker.Result res = this.checker.newResult();
		this.checker.check(com, 0, com.getSize(), reader::read, res);
		if (!res.isCounterExample()) {
			return false;
		}
		this.bad.compareAndSet(null, com);
		return true;
	}

	private AbstractDiskGraph.NodeReader reader() {
		return this.readers.computeIfAbsent(Thread.currentThread(), t -> {
			try {
				return this.dg.newNodeReader();
			} catch (IOException e) {
				throw new UncheckedIOException(e);
			}
		});
	}

	private void closeReaders() throws IOException {
		IOException ioe = null;
		for (final AbstractDiskGraph.NodeReader r : this.readers.values()) {
			try {
				r.close();
			} catch (IOException e) {
				ioe = e;
			}
		}
		this.readers.clear();
		if (ioe != null) {
			throw ioe;
		}
	}
}
