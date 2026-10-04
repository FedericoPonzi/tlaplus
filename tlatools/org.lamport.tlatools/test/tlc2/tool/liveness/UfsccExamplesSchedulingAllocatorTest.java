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
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;

/**
 * {@link ExamplesSchedulingAllocatorTest} with liveness checked by {@link SccStrategy#UFSCC}, whose
 * counterexample may differ from the one asserted by ExamplesSchedulingAllocatorTest.
 */
public class UfsccExamplesSchedulingAllocatorTest extends ExamplesSchedulingAllocatorTest {

	@Override
	protected void beforeSetUp() {
		UfsccFixture.enable();
	}

	@Override
	protected void beforeTearDown() {
		UfsccFixture.assertUfsccUsed();
	}

	@Test
	@Override
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "PermanentAllocation"));
		UfsccFixture.assertValidLasso(recorder);
		assertUnfairLassoRejected();
	}

	private static void assertUnfairLassoRejected() {
		final ITool tool = TLCGlobals.mainChecker.tool;
		final TLCState init = tool.getInitStates().elementAt(0);
		// Only Request is enabled initially, and it has no fairness.
		UfsccFixture.assertValidLasso(stuttering(init));

		// Stuttering after a request is unfair because WF_vars(Schedule) is enabled.
		final TLCState requested = successors(tool, init).get(0);
		assertRejected(stuttering(init, requested));

		// Same, but the lasso first passes a fair cycle back to init.
		for (final TLCState scheduled : successors(tool, requested)) {
			for (final TLCState allocated : successors(tool, scheduled)) {
				for (final TLCState returned : successors(tool, allocated)) {
					if (returned.fingerPrint() == init.fingerPrint()) {
						assertRejected(stuttering(init, requested, scheduled, allocated, init, requested));
						return;
					}
				}
			}
		}
		fail("No cycle back to init");
	}

	private static void assertRejected(final TestMPRecorder lasso) {
		try {
			UfsccFixture.assertValidLasso(lasso);
		} catch (AssertionError expected) {
			assertEquals("Lasso is unfair or satisfies the property", expected.getMessage());
			return;
		}
		fail("Unfair lasso accepted");
	}

	private static List<TLCState> successors(final ITool tool, final TLCState s) {
		final List<TLCState> succs = new ArrayList<>();
		for (final Action a : tool.getActions()) {
			final StateVec next = tool.getNextStates(a, s);
			for (int i = 0; i < next.size(); i++) {
				succs.add(next.elementAt(i));
			}
		}
		return succs;
	}

	private static TestMPRecorder stuttering(final TLCState... trace) {
		final TestMPRecorder r = new TestMPRecorder();
		r.record(EC.TLC_COUNTER_EXAMPLE);
		for (int i = 0; i < trace.length; i++) {
			r.record(EC.TLC_STATE_PRINT2, new TLCStateInfo(trace[i]), i + 1);
		}
		r.record(EC.TLC_STATE_PRINT3);
		return r;
	}
}
