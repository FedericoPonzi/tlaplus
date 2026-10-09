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
import java.util.Arrays;
import java.util.List;
import java.util.SplittableRandom;
import java.util.function.Consumer;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;
import java.util.concurrent.atomic.AtomicReferenceArray;
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
		 * Called concurrently by the workers with the root of a complete SCC,
		 * whose nodes are {@link UnionFindSccSearch#members(Node)}.
		 * 
		 * @return true to stop the search.
		 */
		boolean found(Node root, int size) throws IOException;
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
	private static final int COMPLETED = -1;

	// A worker picks up to this many nodes from a set's live list at once,
	// which divides the acquisitions of the root's lock.
	private static final int MAX_PICKS = 64;

	private enum Claim {
		DEAD, FOUND, SUCCESS
	}

	/**
	 * Observes the search for trace validation against UFSCC.tla. A worker
	 * holds the tracer's step lock from enter to exit except at yieldStep,
	 * which makes the steps between two yields atomic.
	 */
	interface Tracer {
		void enter(int worker);

		void yieldStep(int worker);

		void exit(int worker);

		void addedRoot(Node n);

		void event(int worker, String action, Object... args);
	}

	private Tracer tracer;

	void setTracer(final Tracer t) {
		this.tracer = t;
	}

	private boolean step(final int p) {
		if (this.tracer != null) {
			this.tracer.yieldStep(p);
		}
		return true;
	}

	private void trace(final int p, final String action, final Object... args) {
		if (this.tracer != null) {
			this.tracer.event(p, action, args);
		}
	}

	private final int workers;
	private final Successors successors;
	private final SccListener listener;
	private final NodeTable nodes;
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
	 * @param expectedNodes Initial capacity of the node table.
	 */
	UnionFindSccSearch(final int workers, final int expectedNodes, final Successors successors,
			final SccListener listener) {
		this.workers = Math.max(1, Math.min(MAX_WORKERS, workers));
		this.nodes = new NodeTable(expectedNodes);
		this.successors = successors;
		this.listener = listener;
	}

	/**
	 * @return The node <fp, tidx>, created with ptr if it does not exist yet.
	 */
	Node node(final long fp, final int tidx, final long ptr) {
		return this.nodes.getOrCreate(fp, tidx, ptr);
	}

	/**
	 * @return The node <fp, tidx> or null if it does not exist.
	 */
	Node get(final long fp, final int tidx) {
		return this.nodes.get(fp, tidx);
	}

	/**
	 * Applies action to the nodes of the given chunk of the node table. Must
	 * not run concurrently with {@link #node(long, int, long)}.
	 */
	void forEachNode(final int chunk, final int chunks, final Consumer<Node> action) {
		this.nodes.forEach(chunk, chunks, action);
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
		if (this.tracer != null) {
			this.tracer.addedRoot(n);
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
			if (this.tracer != null) {
				this.tracer.enter(p);
			}
			final Worker w = new Worker(p);
			int cursor = 0;
			while (step(p) && !this.stop) {
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
			if (this.tracer != null) {
				this.tracer.exit(p);
			}
			synchronized (this.lock) {
				if (--this.running == 0) {
					this.lock.notifyAll();
				}
			}
		}
	}

	private static final class Frame {
		final Node v;
		// The nodes picked from v's set; doubles up to MAX_PICKS with each pick.
		Node[] picked;
		int picks;
		int next;
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
			final Claim c0 = makeClaim(root);
			trace(this.p, "start", root, c0.name());
			if (c0 != Claim.SUCCESS) {
				return;
			}
			push(root);
			while (!this.frames.isEmpty()) {
				step(this.p);
				if (stop) {
					return;
				}
				final Frame f = this.frames.peek();
				if (f.succ != null && f.i < f.succ.length) {
					final Node w = f.succ[f.i++];
					final Claim c = makeClaim(w);
					trace(this.p, "claim", w, c.name());
					switch (c) {
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
							final Node ra = find(this.rStack.peek());
							final Node rb = find(r);
							union(this.rStack.peek(), r);
							if (ra == rb) {
								trace(this.p, "same");
							} else {
								final Node u = find(ra);
								trace(this.p, "merge", u, u == ra ? rb : ra);
							}
						}
						trace(this.p, "united");
						break;
					}
					continue;
				}
				if (f.next < f.picks) {
					trace(this.p, "fetch", f.picked[f.next]);
					f.succ = successors.of(f.picked[f.next++], UnionFindSccSearch.this);
					f.i = 0;
					shuffle(f.succ);
					continue;
				}
				if (f.picks > 0) {
					trace(this.p, "remove", (Object) Arrays.copyOf(f.picked, f.picks));
					removeFromList(f.picked, f.picks);
					f.picks = 0;
					f.next = 0;
					f.succ = null;
				}
				f.picked = f.picked == null ? new Node[1]
						: f.picked.length < MAX_PICKS ? new Node[2 * f.picked.length] : f.picked;
				final int picks = pickFromList(f.v, f.picked);
				if (picks > 0) {
					trace(this.p, "pick", (Object) Arrays.copyOf(f.picked, picks));
					f.picks = picks;
					continue;
				}
				if (picks == COMPLETED) {
					final Node r = find(f.v);
					trace(this.p, "complete", r);
					final boolean bad = report(f.v);
					trace(this.p, "check", r, bad);
					if (bad) {
						stopped = true;
						stop = true;
						return;
					}
				} else {
					trace(this.p, "deadset");
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
		return this.listener.found(r, r.size);
	}

	/**
	 * @return The nodes of the complete SCC whose root is r.
	 */
	static List<Node> members(final Node r) {
		final List<Node> scc = new ArrayList<>(r.size);
		Node m = r;
		do {
			scc.add(m);
			m = m.nextMember;
		} while (m != r);
		return scc;
	}

	/**
	 * @return The root of n's set, which identifies n's SCC once the set is
	 *         complete.
	 */
	static Node root(final Node n) {
		return find(n);
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
	 * Copies up to out.length distinct nodes of n's set that are not fully
	 * explored yet to out.
	 * 
	 * @return The number of copied nodes, 0 if the set is complete, or
	 *         {@link #COMPLETED} if the set is complete and the caller is the
	 *         one to report it.
	 */
	private static int pickFromList(final Node n, final Node[] out) {
		while (true) {
			final Node r = find(n);
			synchronized (r) {
				if (r.parent != r) {
					continue;
				}
				if (r.dead) {
					return 0;
				}
				final Node h = r.liveHead;
				if (h == null) {
					r.dead = true;
					return COMPLETED;
				}
				int k = 0;
				Node x = h;
				do {
					out[k++] = x;
					x = x.liveNext;
				} while (k < out.length && x != h);
				// Rotate to spread the workers over the set.
				r.liveHead = x;
				return k;
			}
		}
	}

	/**
	 * Removes the given nodes, which are of the same set, from the set's live
	 * list.
	 */
	private static void removeFromList(final Node[] ns, final int cnt) {
		while (true) {
			final Node r = find(ns[0]);
			synchronized (r) {
				if (r.parent != r) {
					continue;
				}
				for (int j = 0; j < cnt; j++) {
					final Node n = ns[j];
					if (!n.inLive) {
						continue;
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
				}
				return;
			}
		}
	}

	/**
	 * Maps <fp, tidx> to the node. Unlike a ConcurrentHashMap<Long, Node>, it
	 * does not box the keys, and only creating a node locks (one of many
	 * shards, each of which grows independently).
	 */
	private static final class NodeTable {
		private static final int SHARD_BITS = 10;
		private static final int SHARDS = 1 << SHARD_BITS;

		private static final class Shard {
			// Replaced, never modified, once full: A lock-free get that reads a
			// stale array misses only nodes created concurrently.
			private volatile AtomicReferenceArray<Node> slots;
			private int count;

			Shard(final int capacity) {
				this.slots = new AtomicReferenceArray<>(capacity);
			}

			Node get(final long fp, final int tidx, final int h) {
				final AtomicReferenceArray<Node> a = this.slots;
				final int mask = a.length() - 1;
				for (int i = h & mask;; i = (i + 1) & mask) {
					final Node n = a.get(i);
					if (n == null || (n.fp == fp && n.tidx == tidx)) {
						return n;
					}
				}
			}

			// Caller holds the lock.
			void add(final Node n, final int h) {
				AtomicReferenceArray<Node> a = this.slots;
				if (3 * (this.count + 1) > 2 * a.length()) {
					final AtomicReferenceArray<Node> b = new AtomicReferenceArray<>(2 * a.length());
					for (int i = 0; i < a.length(); i++) {
						final Node m = a.get(i);
						if (m != null) {
							put(b, m, hash(m.fp, m.tidx) >>> SHARD_BITS);
						}
					}
					this.slots = a = b;
				}
				put(a, n, h);
				this.count++;
			}

			private static void put(final AtomicReferenceArray<Node> a, final Node n, final int h) {
				final int mask = a.length() - 1;
				int i = h & mask;
				while (a.get(i) != null) {
					i = (i + 1) & mask;
				}
				a.set(i, n);
			}
		}

		private final Shard[] shards = new Shard[SHARDS];

		NodeTable(final int expectedNodes) {
			final long perShard = Math.max(16, 2L * expectedNodes / SHARDS);
			final int capacity = (int) Math.min(1 << 30, Long.highestOneBit(perShard - 1) << 1);
			for (int i = 0; i < SHARDS; i++) {
				this.shards[i] = new Shard(capacity);
			}
		}

		private static int hash(final long fp, final int tidx) {
			final long h = (fp + tidx) * 0x9E3779B97F4A7C15L;
			return (int) (h ^ (h >>> 32));
		}

		Node get(final long fp, final int tidx) {
			final int h = hash(fp, tidx);
			return this.shards[h & (SHARDS - 1)].get(fp, tidx, h >>> SHARD_BITS);
		}

		Node getOrCreate(final long fp, final int tidx, final long ptr) {
			final int h = hash(fp, tidx);
			final Shard s = this.shards[h & (SHARDS - 1)];
			Node n = s.get(fp, tidx, h >>> SHARD_BITS);
			if (n != null) {
				return n;
			}
			synchronized (s) {
				n = s.get(fp, tidx, h >>> SHARD_BITS);
				if (n == null) {
					n = new Node(fp, tidx, ptr);
					s.add(n, h >>> SHARD_BITS);
				}
				return n;
			}
		}

		void forEach(final int chunk, final int chunks, final Consumer<Node> action) {
			final int from = (int) ((long) SHARDS * chunk / chunks);
			final int to = (int) ((long) SHARDS * (chunk + 1) / chunks);
			for (int i = from; i < to; i++) {
				final AtomicReferenceArray<Node> a = this.shards[i].slots;
				for (int j = 0; j < a.length(); j++) {
					final Node n = a.get(j);
					if (n != null) {
						action.accept(n);
					}
				}
			}
		}
	}
}
