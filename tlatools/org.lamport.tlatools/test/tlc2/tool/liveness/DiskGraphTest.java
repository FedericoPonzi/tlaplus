/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.tool.liveness;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import tlc2.util.BitVector;
import tlc2.util.LongVec;
import tlc2.util.statistics.FixedSizedBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

public class DiskGraphTest {

	private static final IBucketStatistics GRAPH_STATS = new FixedSizedBucketStatistics("Test Dummy", 16);
	private static final int NUMBER_OF_SOLUTIONS = 1;
	private static final int NUMBER_OF_ACTIONS = 0;
	private static final BitVector NO_ACTIONS = null;
	
	protected AbstractDiskGraph getDiskGraph() throws IOException {
		// Have to use dedicated folder for each test. Otherwise tests interfere
		// with each other (e.g. test A reads the disk file of test B)
		return new DiskGraph(createTempDirectory().getAbsolutePath(), NUMBER_OF_SOLUTIONS, GRAPH_STATS);
	}
	
	protected int getTableauIndex() {
		return -1;
	}

	protected File createTempDirectory() throws IOException {
		final File temp;
		temp = File.createTempFile("temp", Long.toString(System.nanoTime()));
		if (!(temp.delete())) {
			throw new IOException("Could not delete temp file: " + temp.getAbsolutePath());
		}
		if (!(temp.mkdir())) {
			throw new IOException("Could not create temp directory: " + temp.getAbsolutePath());
		}
		return temp;
	}
	
	private long[] addChain(final AbstractDiskGraph dg, final int tidx, final int n) throws IOException {
		final long[] ptrs = new long[n];
		for (int i = 0; i < n; i++) {
			final GraphNode node = new GraphNode(i + 1L, tidx);
			// Successors to the next node and the node after that (if any).
			for (int j = 1; j <= 2 && i + j < n; j++) {
				node.addTransition(i + j + 1L, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
						NUMBER_OF_ACTIONS, 2 - j);
			}
			ptrs[i] = dg.addNode(node);
		}
		return ptrs;
	}

	private static void assertSameNode(final GraphNode expected, final GraphNode actual) {
		assertEquals(expected, actual);
		assertEquals(expected.succSize(), actual.succSize());
		assertEquals(expected.getTransition(), actual.getTransition());
	}

	// The reader has to see nodes which are still in the write buffer of the
	// graph's node file.
	@Test
	public void testNodeReaderSeesUnflushedNodes() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		final long[] ptrs = addChain(dg, tidx, 3);

		dg.createCache();
		try (AbstractDiskGraph.NodeReader reader = dg.newNodeReader()) {
			for (int i = 0; i < ptrs.length; i++) {
				assertSameNode(dg.getNode(i + 1L, tidx, ptrs[i]), reader.read(i + 1L, tidx, ptrs[i]));
			}
		}
		dg.destroyCache();
	}

	@Test
	public void testNodeReaderRejectsNegativePtr() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		addChain(dg, getTableauIndex(), 1);
		try (AbstractDiskGraph.NodeReader reader = dg.newNodeReader()) {
			reader.read(1L, getTableauIndex(), -1L);
			fail("Expected IllegalArgumentException");
		} catch (IllegalArgumentException expected) {
		}
	}

	// Readers must not interfere with the graph's own reads (and its file
	// pointer) nor with each other.
	@Test
	public void testNodeReadersConcurrently() throws Exception {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		// Enough nodes to span several 8k buffers of BufferedRandomAccessFile.
		final int n = 5000;
		final long[] ptrs = addChain(dg, tidx, n);
		dg.createCache();
		final GraphNode[] expected = new GraphNode[n];
		for (int i = 0; i < n; i++) {
			expected[i] = dg.getNode(i + 1L, tidx, ptrs[i]);
		}

		final int threads = 4;
		final java.util.concurrent.ExecutorService pool = java.util.concurrent.Executors.newFixedThreadPool(threads + 1);
		try {
			final java.util.List<java.util.concurrent.Future<?>> futures = new java.util.ArrayList<>();
			for (int t = 0; t < threads; t++) {
				final int seed = t;
				futures.add(pool.submit(() -> {
					try (AbstractDiskGraph.NodeReader reader = dg.newNodeReader()) {
						final java.util.Random rnd = new java.util.Random(seed);
						for (int k = 0; k < 4 * n; k++) {
							final int i = rnd.nextInt(n);
							assertSameNode(expected[i], reader.read(i + 1L, tidx, ptrs[i]));
						}
					}
					return null;
				}));
			}
			// Concurrently read through the graph itself.
			futures.add(pool.submit(() -> {
				for (int k = 0; k < 2; k++) {
					for (int i = n - 1; i >= 0; i--) {
						assertSameNode(expected[i], dg.getNode(i + 1L, tidx, ptrs[i]));
					}
				}
				return null;
			}));
			for (java.util.concurrent.Future<?> f : futures) {
				f.get();
			}
		} finally {
			pool.shutdownNow();
			dg.destroyCache();
		}
	}

	@Test
	public void testNodeReadersPerThread() throws Exception {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		final long[] ptrs = addChain(dg, tidx, 1);

		final NodeReaders readers = new NodeReaders(dg);
		final AbstractDiskGraph.NodeReader mine = readers.get();
		assertTrue(mine == readers.get());
		final AbstractDiskGraph.NodeReader[] other = new AbstractDiskGraph.NodeReader[1];
		final Thread t = new Thread(() -> other[0] = readers.get());
		t.start();
		t.join();
		assertNotSame(mine, other[0]);

		readers.close();
		for (final AbstractDiskGraph.NodeReader r : new AbstractDiskGraph.NodeReader[] { mine, other[0] }) {
			try {
				r.read(1L, tidx, ptrs[0]);
				fail("Expected the reader to be closed");
			} catch (IOException expected) {
			}
		}
	}

	@Test
	public void testGetLinkConcurrentlyAfterPrepareForReads() throws Exception {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		// Fill the node ptr table up to its threshold, at which the next
		// (unsynchronized) getLink would grow it.
		final int n = (int) (255 * 0.75);
		final long[] ptrs = addChain(dg, tidx, n);
		dg.prepareForReads();

		final int threads = 4;
		final java.util.concurrent.ExecutorService pool = java.util.concurrent.Executors.newFixedThreadPool(threads);
		try {
			final java.util.List<java.util.concurrent.Future<?>> futures = new java.util.ArrayList<>();
			for (int t = 0; t < threads; t++) {
				futures.add(pool.submit(() -> {
					for (int k = 0; k < 100; k++) {
						for (int i = 0; i < n; i++) {
							assertEquals(ptrs[i], dg.getLink(i + 1L, tidx));
						}
					}
					return null;
				}));
			}
			for (java.util.concurrent.Future<?> f : futures) {
				f.get();
			}
		} finally {
			pool.shutdownNow();
		}
	}

	// The SCC search overwrites the file pointers in the node ptr table with
	// links, which makeNodePtrTblIfStale has to undo. Without links, it must
	// not re-read the (potentially huge) ptr file.
	@Test
	public void testMakeNodePtrTblIfStale() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		final long[] ptrs = addChain(dg, tidx, 3);
		assertFalse(dg.isNodePtrTblStale());

		dg.putLink(1L, tidx, AbstractDiskGraph.MAX_PTR + 1);
		dg.setMaxLink(2L, tidx);
		assertTrue(dg.isNodePtrTblStale());

		dg.makeNodePtrTblIfStale();
		assertFalse(dg.isNodePtrTblStale());
		for (int i = 0; i < ptrs.length; i++) {
			assertEquals(ptrs[i], dg.getLink(i + 1L, tidx));
		}
	}

	// DiskGraph#getPath marks nodes in the node ptr table.
	@Test
	public void testMakeNodePtrTblIfStaleAfterGetPath() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		dg.addInitNode(1L, tidx);
		final long[] ptrs = addChain(dg, tidx, 4);
		dg.createCache();
		dg.getPath(4L, tidx);
		dg.destroyCache();

		dg.makeNodePtrTblIfStale();
		for (int i = 0; i < ptrs.length; i++) {
			assertEquals(ptrs[i], dg.getLink(i + 1L, tidx));
		}
	}

	// No init node makes DiskGraph#getPath never break from the while loop
	@Test
	public void testGetPathWithoutInitNoTableau() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		dg.addNode(new GraphNode(1L, tidx));
		dg.createCache();
		try {
			dg.getPath(1L, -1);
		} catch (RuntimeException e) {
			return;
		}
		fail("getPath() without init nodes has to throw a RuntimeException");
	}

	// Create a linear minimal graph (2 nodes) and check if the graph is
	// returned by getPath afterwards.
	@Test
	public void testGetMinimalPathWithoutTableau() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();

		final long initFP = 1L;
		final long successorFP = 2L;
		
		// Init node
		dg.addInitNode(1L, tidx);

		// Successor node
		dg.addNode(new GraphNode(successorFP, tidx));
		
		// Create relationship between init and successor
		final GraphNode node = new GraphNode(initFP, tidx);
		node.addTransition(successorFP, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS, NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);

		// Can only lookup/get a node, if there is a cache
		dg.createCache();
		final LongVec path = dg.getPath(successorFP, tidx);
		dg.destroyCache();

		assertFalse("Length or path returned is too short", path.size() < 2);
		assertFalse("Length or path returned is too long", path.size() > 2);
	}
	
	/*
	 * +----------+                   
	 * |          |                   
	 * | init     |                   
	 * |          |                   
	 * |          |                   
	 * +----------+                   
	 *                                
	 * +----------+       +----------+
	 * |          |       |          |
	 * | second   +------->  final   |
	 * | init     |       |          |
	 * |          |       |          |
	 * +----------+       +----------+
	 * 
	 * The specialty here is that there are *two* init nodes and one of them has *no* successors.
	 * 
	 * @see Bug #293 in general/bugzilla/index.html
	 */
	@Test
	public void testPathWithTwoInitNodes() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();

		long noSuccessorInitState = 1L;

		long regularInitState = 2L;
		
		long finalState = 3L;

		// Init
		dg.addInitNode(noSuccessorInitState, tidx);
		
		/*
		 * Intentionally *NOT* adding the init via dg.addNode(init)
		 */
		
		// second init (this one gets added via addNode
		dg.addInitNode(regularInitState, tidx);
		GraphNode node = new GraphNode(regularInitState, tidx);
		node.addTransition(finalState, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		
		// final
		node = new GraphNode(finalState, tidx);
		dg.addNode(node);
		
		dg.createCache();
		LongVec path = dg.getPath(finalState, tidx);
		dg.destroyCache();
		
		assertEquals(2, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(regularInitState, path.elementAt(1));

		// Make sure it also returns a path if init is searched
		dg.createCache();
		path = dg.getPath(noSuccessorInitState, tidx);
		dg.destroyCache();

		assertEquals(1, path.size());
		assertEquals(noSuccessorInitState, path.elementAt(0));
	}
	
	/*
	 * Make sure the same logical node isn't counted twice.
	 */
	@Test
	public void testAddSameGraphNodeTwice() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		dg.addNode(new GraphNode(1L, 1));
		dg.addNode(new GraphNode(1L, 1));
		assertEquals(1, dg.size());
	}
	
	
	/*
	 * Test that it is possible to "update" a GraphNode's outgoing transitions.
	 */
	@Test
	public void testLookupExistingNode() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		
		GraphNode node = dg.getNode(1L, tidx);
		assertEquals(0, node.succSize());
		dg.addNode(node);
		
		// Cause the DiskGraph to be read from disk
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, tidx);
		dg.addNode(node);
		assertEquals(0, node.succSize());
		
		node.addTransition(2, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(1, node.succSize());
		assertTrue(node.transExists(2, tidx));
		
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, tidx);
		assertEquals(1, node.succSize());

		node.addTransition(3, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, tidx));
		assertTrue(node.transExists(3, tidx));
		
		// commit/chkpt
		dg.beginChkpt();
		dg.commitChkpt();
		dg.recover();
		
		node = dg.getNode(1L, tidx);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, tidx));
		assertTrue(node.transExists(3, tidx));
	}
	
	/*
	 * Test that adding a GraphNode twice (same fingerprint & tableau idx) but
	 * with different successors afterwards yields the union of the successors.
	 */
	@Test
	public void testAddSameGraphNodeTwiceCorrectSuccessors() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		
		// Add a graphnode to DiskGraph with a single transition
		final GraphNode graphNode = dg.getNode(1, tidx);
		graphNode.addTransition(2, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		long firstPtr = dg.addNode(graphNode);
		
		// Update the same graph node with another transition
		final GraphNode graphNodeSecondInstance = dg.getNode(1, tidx);
		graphNodeSecondInstance.addTransition(3, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		long secondPtr = dg.addNode(graphNodeSecondInstance);
		
		assertEquals(1, dg.size());
		
		assertNotSame(firstPtr, secondPtr);
		assertEquals(secondPtr, dg.getLink(1, tidx));

		final GraphNode node = dg.getNode(1, tidx);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, tidx));
		assertTrue(node.transExists(3, tidx));
		
		dg.makeNodePtrTbl();
		dg.createCache();
		final long ptr = dg.getLink(1, tidx);
		final GraphNode n = dg.getNode(1, tidx, ptr);
		assertEquals(2, n.succSize());
		assertTrue(n.transExists(2, tidx));
		assertTrue(n.transExists(3, tidx));
	}
	
	/*
	 * Test to verify that getPath does not throw an ArrayIndexOutOfBounds due
	 * to nextLoc being -1. This used to happen intermittently when liveness
	 * checking runs periodically on an incomplete state/behavior graph, a
	 * liveness violation is found and the path of the error trace gets explored.
	 */
	@Test
	public void testGetPathPartialGraph() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		final int tidx = getTableauIndex();
		
		final long initState = 2L;
		final long danglingState = 3L;

		// Init
		dg.addInitNode(initState, tidx);
		final GraphNode node = new GraphNode(initState, tidx);
		node.addTransition(danglingState, tidx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);

		/*
		 * The dangling state does not get added on purpose to simulate a
		 * partial graph.
		 */
	
		// Now get the path to some non-existing state (to explore all states in
		// the graph)
		dg.createCache();
		try {
			dg.getPath(5L, tidx);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail(e.getMessage());
		} catch (RuntimeException e) {
			// Make sure it is the correct RuntimeException
			assertEquals("Couldn't re-create liveness trace (path) starting at: 5 and tidx: " + tidx, e.getMessage());
		}
	}
}
