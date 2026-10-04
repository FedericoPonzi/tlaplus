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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.SplittableRandom;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;
import java.util.concurrent.atomic.AtomicReference;

/**
 * {@link SccStrategy#UFSCC}: Multi-core on-the-fly SCC search of V. Bloemen,
 * A. Laarman, J. van de Pol, "Multi-Core On-The-Fly SCC Decomposition", PPoPP
 * 2016 (Algorithm 2). The workers run (randomized) depth-first searches that
 * share a union-find structure: a worker that finds a cycle unites the sets on
 * its stack, and all workers then explore the united set together. A set whose
 * nodes have all been explored is a complete SCC and is reported exactly once,
 * to the {@link SccListener}, by the worker that completed it.
 * <p>
 * Unlike the paper's lock-free variant, a set's live list is guarded by the
 * lock of the set's root, which keeps the implementation simple.
 */
final class UnionFindSccSearch {

	/** The worker bitsets are longs. */
	static final int MAX_WORKERS = Long.SIZE;

	interface Successors {
		/**
		 * @return The successors of node that the search follows. Successors that
		 *         are not followed but have to be searched nonetheless are passed
		 *         to {@link UnionFindSccSearch#addRoot(Node)}.
		 */
		Node[] of(Node node, UnionFindSccSearch search) throws IOException;
	}

	interface SccListener {
		/**
		 * Called concurrently by the workers.
		 * 
		 * @return true to stop the search.
		 */
		boolean found(List<Node> scc) throws IOException;
	}

	static final class Node {
		final long fp;
		final int tidx;
		// Unique; also orders the locks of two roots.
		final long ptr;

		private volatile Node parent = this;
		// The following fields are only meaningful while this is a root.
		private int size = 1;
		private volatile long workers;
		private volatile boolean dead;
		private Node liveHead = this;

		// Doubly-linked ring of the nodes not yet fully explored, guarded by the
		// lock of the set's root.
		private Node liveNext = this;
		private Node livePrev = this;
		private boolean inLive = true;

		// Ring of all nodes of the set.
		private Node nextMember = this;

		private volatile int queued;

		Node(final long fp, final int tidx, final long ptr) {
			this.fp = fp;
			this.tidx = tidx;
			this.ptr = ptr;
		}

		@Override
		public String toString() {
			return "<" + fp + "," + tidx + "," + ptr + ">";
		}
	}

	private static final AtomicIntegerFieldUpdater<Node> QUEUED = AtomicIntegerFieldUpdater.newUpdater(Node.class,
			"queued");

	// Returned by pickFromList to the worker that found the set to be complete.
	private static final Node COMPLETED = new Node(-1, -1, -1);

	private enum Claim {
		DEAD, FOUND, SUCCESS
	}

	private final int workers;
	private final Successors successors;
	private final SccListener listener;
	private final ConcurrentHashMap<Long, Node> nodes;
	private final List<Node> roots = new ArrayList<>();
	private final AtomicReference<Throwable> failure = new AtomicReference<>();
	private volatile boolean stop = false;
	private volatile boolean stopped = false;

	// run() waits for the workers that started to finish.
	private final Object lock = new Object();
	private int running = 0;
	private boolean closed = false;

	UnionFindSccSearch(final int workers, final Successors successors, final SccListener listener) {
		this(workers, 16, successors, listener);
	}

	/**
	 * @param expectedNodes Sizes the node map, which is expensive to grow.
	 */
	UnionFindSccSearch(final int workers, final int expectedNodes, final Successors successors,
			final SccListener listener) {
		this.workers = Math.max(1, Math.min(MAX_WORKERS, workers));
		this.nodes = new ConcurrentHashMap<>(expectedNodes);
		this.successors = successors;
		this.listener = listener;
	}

	/**
	 * @return The node with the given ptr, created if it does not exist yet.
	 */
	Node node(final long fp, final int tidx, final long ptr) {
		final Node n = this.nodes.get(ptr);
		if (n != null) {
			return n;
		}
		return this.nodes.computeIfAbsent(ptr, p -> new Node(fp, tidx, ptr));
	}

	/**
	 * Schedules the search of node unless it has been scheduled or completed
	 * already.
	 */
	void addRoot(final Node n) {
		if (find(n).dead || !QUEUED.compareAndSet(n, 0, 1)) {
			return;
		}
		synchronized (this.roots) {
			this.roots.add(n);
		}
	}

	/**
	 * @return true iff the {@link SccListener} stopped the search.
	 */
	boolean isStopped() {
		return this.stopped;
	}

	/**
	 * Searches the SCCs reachable from the roots with one worker running in the
	 * calling thread and the others in pool (if not null). Returns after all
	 * workers have finished.
	 */
	void run(final ExecutorService pool) throws IOException, InterruptedException {
		final List<Future<?>> futures = new ArrayList<>();
		if (pool != null) {
			for (int p = 1; p < this.workers; p++) {
				final int id = p;
				futures.add(pool.submit(() -> work(id)));
			}
		}
		try {
			work(0);
			for (final Future<?> f : futures) {
				f.get();
			}
		} catch (ExecutionException e) {
			// work() does not throw.
			throw new IllegalStateException(e.getCause());
		} finally {
			this.stop = true;
			awaitWorkers();
		}
		final Throwable t = this.failure.get();
		if (t instanceof IOException) {
			throw (IOException) t;
		} else if (t instanceof InterruptedException) {
			throw (InterruptedException) t;
		} else if (t instanceof RuntimeException) {
			throw (RuntimeException) t;
		} else if (t instanceof Error) {
			throw (Error) t;
		} else if (t != null) {
			throw new IllegalStateException(t);
		}
	}

	private void awaitWorkers() {
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
	}

	private void work(final int p) {
		synchronized (this.lock) {
			if (this.closed) {
				return;
			}
			this.running++;
		}
		try {
			final Worker w = new Worker(p);
			int cursor = 0;
			while (!this.stop) {
				final Node root;
				synchronized (this.roots) {
					if (cursor >= this.roots.size()) {
						break;
					}
					root = this.roots.get(cursor++);
				}
				w.search(root);
			}
		} catch (Throwable t) {
			this.failure.compareAndSet(null, t);
			this.stop = true;
		} finally {
			synchronized (this.lock) {
				if (--this.running == 0) {
					this.lock.notifyAll();
				}
			}
		}
	}

	private static final class Frame {
		final Node v;
		Node cur;
		Node[] succ;
		int i;

		Frame(final Node v) {
			this.v = v;
		}
	}

	private final class Worker {
		private final int p;
		private final long bit;
		// Worker 0 follows the successors in order, the others in random order
		// to spread the workers over the graph.
		private final SplittableRandom rnd;
		private final ArrayDeque<Frame> frames = new ArrayDeque<>();
		private final ArrayDeque<Node> rStack = new ArrayDeque<>();

		Worker(final int p) {
			this.p = p;
			this.bit = 1L << p;
			this.rnd = p == 0 ? null : new SplittableRandom(p);
		}

		void search(final Node root) throws IOException {
			if (makeClaim(root) != Claim.SUCCESS) {
				return;
			}
			push(root);
			while (!this.frames.isEmpty()) {
				if (stop) {
					return;
				}
				final Frame f = this.frames.peek();
				if (f.succ != null && f.i < f.succ.length) {
					final Node w = f.succ[f.i++];
					switch (makeClaim(w)) {
					case DEAD:
						break;
					case SUCCESS:
						push(w);
						break;
					case FOUND:
						// w's set is on this worker's stack: Unite the sets on the
						// stack down to w's.
						while (!sameSet(f.v, w)) {
							final Node r = this.rStack.pop();
							if (this.rStack.isEmpty()) {
								throw new IllegalStateException("UFSCC: " + w + " not on the stack of worker " + this.p);
							}
							union(this.rStack.peek(), r);
						}
						break;
					}
					continue;
				}
				if (f.cur != null) {
					removeFromList(f.cur);
					f.cur = null;
					f.succ = null;
				}
				final Node next = pickFromList(f.v);
				if (next != null && next != COMPLETED) {
					f.cur = next;
					f.succ = successors.of(next, UnionFindSccSearch.this);
					f.i = 0;
					shuffle(f.succ);
					continue;
				}
				if (next == COMPLETED && report(f.v)) {
					stopped = true;
					stop = true;
					return;
				}
				if (this.rStack.peek() == f.v) {
					this.rStack.pop();
				}
				this.frames.pop();
			}
		}

		private void push(final Node n) {
			this.rStack.push(n);
			this.frames.push(new Frame(n));
		}

		private void shuffle(final Node[] a) {
			if (this.rnd == null) {
				return;
			}
			for (int i = a.length - 1; i > 0; i--) {
				final int j = this.rnd.nextInt(i + 1);
				final Node t = a[i];
				a[i] = a[j];
				a[j] = t;
			}
		}

		private Claim makeClaim(final Node n) {
			while (true) {
				final Node r = find(n);
				if (r.dead) {
					return Claim.DEAD;
				}
				if ((r.workers & this.bit) != 0) {
					if (r.parent == r) {
						return Claim.FOUND;
					}
					continue;
				}
				synchronized (r) {
					if (r.parent != r) {
						continue;
					}
					if (r.dead) {
						return Claim.DEAD;
					}
					if ((r.workers & this.bit) != 0) {
						return Claim.FOUND;
					}
					r.workers |= this.bit;
					return Claim.SUCCESS;
				}
			}
		}
	}

	private boolean report(final Node n) throws IOException {
		final Node r = find(n);
		final List<Node> scc = new ArrayList<>(r.size);
		Node m = r;
		do {
			scc.add(m);
			m = m.nextMember;
		} while (m != r);
		return this.listener.found(scc);
	}

	private static Node find(final Node n) {
		Node x = n;
		while (true) {
			final Node p = x.parent;
			if (p == x) {
				return x;
			}
			final Node gp = p.parent;
			if (gp != p) {
				// Path halving; x is no root, so its parent only moves up.
				x.parent = gp;
			}
			x = gp;
		}
	}

	private static boolean sameSet(final Node a, final Node b) {
		while (true) {
			final Node ra = find(a);
			final Node rb = find(b);
			if (ra == rb) {
				return true;
			}
			if (ra.parent == ra) {
				return false;
			}
		}
	}

	private static void union(final Node a, final Node b) {
		while (true) {
			final Node ra = find(a);
			final Node rb = find(b);
			if (ra == rb) {
				return;
			}
			final Node first = ra.ptr < rb.ptr ? ra : rb;
			final Node second = first == ra ? rb : ra;
			synchronized (first) {
				synchronized (second) {
					if (ra.parent != ra || rb.parent != rb) {
						continue;
					}
					if (ra.dead || rb.dead) {
						throw new IllegalStateException("UFSCC: union of a completed SCC " + ra + " " + rb);
					}
					final Node root = ra.size >= rb.size ? ra : rb;
					final Node child = root == ra ? rb : ra;

					// Link first: A worker that sees its bit on root must also
					// see its own set united with root (see makeClaim/sameSet).
					child.parent = root;
					root.size += child.size;

					if (child.liveHead != null) {
						if (root.liveHead == null) {
							root.liveHead = child.liveHead;
						} else {
							final Node a1 = root.liveHead;
							final Node b1 = child.liveHead;
							final Node an = a1.liveNext;
							final Node bn = b1.liveNext;
							a1.liveNext = bn;
							bn.livePrev = a1;
							b1.liveNext = an;
							an.livePrev = b1;
						}
						child.liveHead = null;
					}

					final Node m = root.nextMember;
					root.nextMember = child.nextMember;
					child.nextMember = m;

					root.workers |= child.workers;
					return;
				}
			}
		}
	}

	/**
	 * @return A node of n's set that is not fully explored yet, null if the set
	 *         is complete, or {@link #COMPLETED} if the set is complete and the
	 *         caller is the one to report it.
	 */
	private static Node pickFromList(final Node n) {
		while (true) {
			final Node r = find(n);
			synchronized (r) {
				if (r.parent != r) {
					continue;
				}
				if (r.dead) {
					return null;
				}
				final Node h = r.liveHead;
				if (h == null) {
					r.dead = true;
					return COMPLETED;
				}
				// Rotate to spread the workers over the set.
				r.liveHead = h.liveNext;
				return h;
			}
		}
	}

	private static void removeFromList(final Node n) {
		while (true) {
			final Node r = find(n);
			synchronized (r) {
				if (r.parent != r) {
					continue;
				}
				if (!n.inLive) {
					return;
				}
				n.inLive = false;
				if (n.liveNext == n) {
					r.liveHead = null;
				} else {
					n.livePrev.liveNext = n.liveNext;
					n.liveNext.livePrev = n.livePrev;
					if (r.liveHead == n) {
						r.liveHead = n.liveNext;
					}
				}
				n.liveNext = n;
				n.livePrev = n;
				return;
			}
		}
	}
}
