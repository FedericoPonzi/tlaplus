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
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicLong;

import tlc2.util.IntStack;

/**
 * {@link SccStrategy#PIPELINE}: While {@link LiveWorker}'s Tarjan search
 * continues to find SCCs, the SCCs it has already found are checked by a pool
 * of threads, each reading the disk graph with its own
 * {@link AbstractDiskGraph.NodeReader}. Small SCCs are batched, large ones are
 * split across all threads.
 * <p>
 * Results are consumed in the order in which the SCCs were found. Thus, the
 * violation reported is the one {@link SccStrategy#TARJAN} would report, and so
 * is the counterexample.
 * <p>
 * Not thread-safe: all methods but the tasks it submits are called by the
 * thread running the Tarjan search.
 */
final class PipelinedComponentChecker implements AutoCloseable {

	static final String BATCH_PROPERTY = LiveCheck.class.getName() + ".sccBatchSize";
	static final String SPLIT_PROPERTY = LiveCheck.class.getName() + ".sccSplitSize";

	// For tests to assert the pipeline was used.
	static final AtomicLong DISPATCHED = new AtomicLong();
	static final AtomicLong SPLITS = new AtomicLong();

	/**
	 * An SCC found by the Tarjan search, identified by its root <state, tidx>.
	 */
	static final class Component {
		final long state;
		final int tidx;
		private final long loc;
		// null for an SCC with a single node, which is only created (by a pool
		// thread) if the node stutters.
		TableauNodePtrTable com;

		private Component(final long state, final int tidx, final long loc, final TableauNodePtrTable com) {
			this.state = state;
			this.tidx = tidx;
			this.loc = loc;
			this.com = com;
		}
	}

	private final ExecutorService pool;
	private final int workers;
	private final ComponentChecker checker;
	private final AbstractDiskGraph dg;
	private final int batchSize;
	private final int splitSize;
	private final int maxInFlight;

	private final ArrayDeque<Future<Component>> inFlight = new ArrayDeque<>();
	private final Map<Thread, AbstractDiskGraph.NodeReader> readers = new ConcurrentHashMap<>();
	private List<Component> batch = new ArrayList<>();
	private long batchNodes = 0L;
	private volatile boolean aborted = false;

	// Readers may only be closed once no task uses them anymore.
	private final Object lock = new Object();
	private int running = 0;
	private boolean closed = false;

	PipelinedComponentChecker(final ExecutorService pool, final int workers, final ComponentChecker checker,
			final AbstractDiskGraph dg) {
		this.pool = pool;
		this.workers = workers;
		this.checker = checker;
		this.dg = dg;
		this.batchSize = Math.max(1, Integer.getInteger(BATCH_PROPERTY, 4096));
		this.splitSize = Math.max(1, Integer.getInteger(SPLIT_PROPERTY, 1 << 16));
		this.maxInFlight = 4 * workers;
	}

	/**
	 * Pops the SCC rooted at <state, tidx> off comStack (see
	 * LiveWorker#checkComponent) and schedules it to be checked.
	 * 
	 * @return The earliest SCC (in the order of calls to this method) known to
	 *         violate liveness, or null if none is known yet.
	 */
	Component add(final long state, final int tidx, final IntStack comStack)
			throws IOException, InterruptedException {
		long state1 = comStack.popLong();
		int tidx1 = comStack.popInt();
		long loc1 = comStack.popLong();

		if (state1 == state && tidx1 == tidx) {
			this.dg.setMaxLink(state, tidx);
			return enqueue(new Component(state, tidx, loc1, null), 1);
		}

		// Same as LiveWorker#checkComponent.
		final TableauNodePtrTable com = new TableauNodePtrTable(128);
		while (true) {
			com.put(state1, tidx1, loc1);
			assert AbstractDiskGraph.isFilePointer(loc1);
			this.dg.setMaxLink(state1, tidx1);
			if (state == state1 && tidx == tidx1) {
				break;
			}
			state1 = comStack.popLong();
			tidx1 = comStack.popInt();
			loc1 = comStack.popLong();
		}
		LiveWorker.STATS.addSample(com.size());
		com.prepareForReads();

		final Component c = new Component(state, tidx, loc1, com);
		if (com.size() < this.splitSize) {
			return enqueue(c, com.size());
		}

		// Check the SCCs found before this one first to report the earliest.
		submitBatch();
		final Component earlier = drain();
		if (earlier != null) {
			return earlier;
		}
		return checkSplit(c) ? c : null;
	}

	/**
	 * Waits for all scheduled SCCs to be checked.
	 * 
	 * @return The earliest SCC that violates liveness or null.
	 */
	Component finish() throws IOException, InterruptedException {
		submitBatch();
		return drain();
	}

	private Component enqueue(final Component c, final int nodes) throws IOException, InterruptedException {
		this.batch.add(c);
		this.batchNodes += nodes;
		if (this.batchNodes >= this.batchSize) {
			submitBatch();
		}
		// Consume completed results in order without blocking unless too many
		// batches are in flight (back-pressure on the Tarjan search).
		while (!this.inFlight.isEmpty() && (this.inFlight.peekFirst().isDone() || this.inFlight.size() > this.maxInFlight)) {
			final Component bad = get(this.inFlight.pollFirst());
			if (bad != null) {
				abort();
				return bad;
			}
		}
		return null;
	}

	private void submitBatch() {
		if (this.batch.isEmpty()) {
			return;
		}
		final List<Component> components = this.batch;
		this.batch = new ArrayList<>();
		this.batchNodes = 0L;
		this.inFlight.addLast(this.pool.submit(tracked(() -> {
			final AbstractDiskGraph.NodeReader reader = reader();
			for (final Component c : components) {
				if (this.aborted) {
					return null;
				}
				if (isCounterExample(c, reader)) {
					return c;
				}
			}
			return null;
		})));
	}

	private boolean isCounterExample(final Component c, final AbstractDiskGraph.NodeReader reader)
			throws IOException {
		if (c.com == null) {
			// Trivial unless the single node stutters (see LiveWorker#checkComponent).
			if (!this.checker.isStuttering(reader.read(c.state, c.tidx, c.loc))) {
				return false;
			}
			final TableauNodePtrTable com = new TableauNodePtrTable(128);
			com.put(c.state, c.tidx, c.loc);
			com.prepareForReads();
			c.com = com;
		}
		DISPATCHED.incrementAndGet();
		final ComponentChecker.Result res = this.checker.newResult();
		this.checker.check(c.com, 0, c.com.getSize(), reader::read, res);
		return res.isCounterExample();
	}

	private boolean checkSplit(final Component c) throws IOException, InterruptedException {
		DISPATCHED.incrementAndGet();
		SPLITS.incrementAndGet();
		final TableauNodePtrTable com = c.com;
		final int size = com.getSize();
		final List<Callable<ComponentChecker.Result>> chunks = new ArrayList<>(this.workers);
		for (int i = 0; i < this.workers; i++) {
			final int from = (int) ((long) size * i / this.workers);
			final int to = (int) ((long) size * (i + 1) / this.workers);
			chunks.add(tracked(() -> {
				final ComponentChecker.Result res = this.checker.newResult();
				this.checker.check(com, from, to, reader()::read, res);
				return res;
			}));
		}
		final ComponentChecker.Result res = this.checker.newResult();
		for (final Future<ComponentChecker.Result> f : this.pool.invokeAll(chunks)) {
			res.or(get(f));
		}
		return res.isCounterExample();
	}

	private Component drain() throws IOException, InterruptedException {
		while (!this.inFlight.isEmpty()) {
			final Component bad = get(this.inFlight.pollFirst());
			if (bad != null) {
				abort();
				return bad;
			}
		}
		return null;
	}

	/**
	 * Stops checking the SCCs still in flight and waits for the pool threads to
	 * stop reading the disk graph.
	 */
	private void abort() {
		this.aborted = true;
		this.batch.clear();
		this.batchNodes = 0L;
		while (!this.inFlight.isEmpty()) {
			try {
				this.inFlight.pollFirst().get();
			} catch (InterruptedException e) {
				Thread.currentThread().interrupt();
				return;
			} catch (ExecutionException | CancellationException ignored) {
				// Superseded by the earlier violation or exception.
			}
		}
	}

	private <T> Callable<T> tracked(final Callable<T> task) {
		return () -> {
			synchronized (this.lock) {
				if (this.closed) {
					throw new CancellationException();
				}
				this.running++;
			}
			try {
				return task.call();
			} finally {
				synchronized (this.lock) {
					if (--this.running == 0) {
						this.lock.notifyAll();
					}
				}
			}
		};
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

	static <T> T get(final Future<T> f) throws IOException, InterruptedException {
		try {
			return f.get();
		} catch (ExecutionException e) {
			final Throwable cause = e.getCause();
			if (cause instanceof UncheckedIOException) {
				throw ((UncheckedIOException) cause).getCause();
			} else if (cause instanceof IOException) {
				throw (IOException) cause;
			} else if (cause instanceof RuntimeException) {
				throw (RuntimeException) cause;
			} else if (cause instanceof Error) {
				throw (Error) cause;
			}
			throw new RuntimeException(cause);
		}
	}

	@Override
	public void close() throws IOException {
		abort();
		boolean interrupted = false;
		synchronized (this.lock) {
			this.closed = true;
			while (this.running > 0) {
				try {
					this.lock.wait();
				} catch (InterruptedException e) {
					interrupted = true;
				}
			}
		}
		if (interrupted) {
			Thread.currentThread().interrupt();
		}
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
