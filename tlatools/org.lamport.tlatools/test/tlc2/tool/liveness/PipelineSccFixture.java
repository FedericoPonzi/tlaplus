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

import static org.junit.Assert.assertTrue;

/**
 * Makes a {@link ModelCheckerTestCase} check liveness with
 * {@link SccStrategy#PIPELINE} and tiny batches, so that the inherited
 * assertions (incl. the exact counterexample) verify the pipeline behaves
 * exactly like {@link SccStrategy#TARJAN}.
 */
final class PipelineSccFixture {

	private PipelineSccFixture() {
	}

	/**
	 * @param splitSize SCCs with at least this many nodes are checked by all
	 *                  workers in parallel.
	 */
	static void enable(final int batchSize, final int splitSize) {
		System.setProperty(SccStrategy.PROPERTY, "pipeline");
		System.setProperty(SccStrategy.WORKERS_PROPERTY, "4");
		System.setProperty(PipelinedComponentChecker.BATCH_PROPERTY, Integer.toString(batchSize));
		System.setProperty(PipelinedComponentChecker.SPLIT_PROPERTY, Integer.toString(splitSize));
		PipelinedComponentChecker.DISPATCHED.set(0);
		PipelinedComponentChecker.SPLITS.set(0);
	}

	static void assertPipelineUsed(final boolean expectSplits) {
		assertTrue("No component checked by the pipeline", PipelinedComponentChecker.DISPATCHED.get() > 0);
		if (expectSplits) {
			assertTrue("No component split across workers", PipelinedComponentChecker.SPLITS.get() > 0);
		}
		System.clearProperty(SccStrategy.PROPERTY);
		System.clearProperty(SccStrategy.WORKERS_PROPERTY);
		System.clearProperty(PipelinedComponentChecker.BATCH_PROPERTY);
		System.clearProperty(PipelinedComponentChecker.SPLIT_PROPERTY);
	}
}
