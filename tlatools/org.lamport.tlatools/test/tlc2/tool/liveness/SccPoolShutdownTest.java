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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.nio.file.Files;
import java.util.concurrent.CancellationException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.After;
import org.junit.Test;

import tlc2.util.MemIntStack;
import tlc2.util.statistics.FixedSizedBucketStatistics;

/**
 * LiveCheck shuts the SCC pool down while LiveWorkers may still wait for tasks
 * queued in it (e.g. when interrupted). The waiters must not hang.
 */
public class SccPoolShutdownTest {

	private interface Body {
		void run() throws Exception;
	}

	private final CountDownLatch release = new CountDownLatch(1);
	private final ThreadPoolExecutor pool = (ThreadPoolExecutor) Executors.newFixedThreadPool(1);

	@After
	public void tearDown() {
		release.countDown();
		pool.shutdownNow();
	}

	@Test(timeout = 60000)
	public void testPipelineWaitingForDroppedBatch() throws Exception {
		final PipelinedComponentChecker pipeline = new PipelinedComponentChecker(pool, 1, null, newDiskGraph());
		assertUnblockedByShutdown(1, () -> {
			try {
				pipeline.add(1L, -1, singleton(1L));
				pipeline.finish();
			} finally {
				pipeline.close();
			}
		});
	}

	@Test(timeout = 60000)
	public void testPipelineClosesWithDroppedBatches() throws Exception {
		System.setProperty(PipelinedComponentChecker.BATCH_PROPERTY, "1");
		try {
			final PipelinedComponentChecker pipeline = new PipelinedComponentChecker(pool, 1, null,
					newDiskGraph());
			final AtomicReference<Throwable> closeFailure = new AtomicReference<>();
			assertUnblockedByShutdown(3, () -> {
				try {
					for (long fp = 1L; fp <= 3L; fp++) {
						pipeline.add(fp, -1, singleton(fp));
					}
					pipeline.finish();
				} finally {
					try {
						pipeline.close();
					} catch (Throwable t) {
						closeFailure.set(t);
					}
				}
			});
			assertTrue("close() failed: " + closeFailure.get(), closeFailure.get() == null);
		} finally {
			System.clearProperty(PipelinedComponentChecker.BATCH_PROPERTY);
		}
	}

	/**
	 * Runs body in a thread while the pool's only thread is busy, so that body
	 * waits for tasks queued behind it, then shuts the pool down.
	 */
	private void assertUnblockedByShutdown(final int queued, final Body body) throws Exception {
		pool.submit(() -> {
			release.await();
			return null;
		});
		final AtomicReference<Throwable> failure = new AtomicReference<>();
		final Thread t = new Thread(() -> {
			try {
				body.run();
			} catch (Throwable e) {
				failure.set(e);
			}
		});
		t.start();
		while (pool.getQueue().size() < queued || t.getState() != Thread.State.WAITING) {
			assertTrue("Body finished before waiting", t.isAlive());
			Thread.sleep(10);
		}

		LiveCheck.shutdownNow(pool);
		t.join(10000);
		final boolean hangs = t.isAlive();
		t.interrupt();
		assertFalse("Waiter still blocked after shutdown", hangs);
		assertTrue("Expected CancellationException but was " + failure.get(),
				failure.get() instanceof CancellationException);
	}

	private static AbstractDiskGraph newDiskGraph() throws Exception {
		final File dir = Files.createTempDirectory("sccpool").toFile();
		dir.deleteOnExit();
		return new DiskGraph(dir.getAbsolutePath(), 1, new FixedSizedBucketStatistics("Test", 16));
	}

	// An SCC of a single node, laid out as on LiveWorker's comStack.
	private static MemIntStack singleton(final long fp) {
		final MemIntStack stack = new MemIntStack(null, "com");
		stack.pushLong(0L);
		stack.pushInt(-1);
		stack.pushLong(fp);
		return stack;
	}
}
