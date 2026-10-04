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

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import tla2sany.semantic.ExprNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.TestMPRecorder;

/**
 * Makes a {@link ModelCheckerTestCase} check liveness with
 * {@link SccStrategy#UFSCC}. Its counterexample may differ from
 * {@link SccStrategy#TARJAN}'s, thus tests that assert an exact
 * counterexample assert {@link #assertValidLasso(TestMPRecorder)} instead.
 */
final class UfsccFixture {

	private UfsccFixture() {
	}

	static void enable() {
		System.setProperty(SccStrategy.PROPERTY, "ufscc");
		System.setProperty(SccStrategy.WORKERS_PROPERTY, "4");
		// Split all SCCs across the workers.
		System.setProperty(PipelinedComponentChecker.SPLIT_PROPERTY, "1");
		UnionFindComponentChecker.SEARCHES.set(0);
		UnionFindComponentChecker.SPLITS.set(0);
	}

	static void assertUfsccUsed() {
		assertTrue("No SCC search by UFSCC", UnionFindComponentChecker.SEARCHES.get() > 0);
		assertTrue("No SCC split across workers", UnionFindComponentChecker.SPLITS.get() > 0);
		System.clearProperty(SccStrategy.PROPERTY);
		System.clearProperty(SccStrategy.WORKERS_PROPERTY);
		System.clearProperty(PipelinedComponentChecker.SPLIT_PROPERTY);
	}

	/**
	 * Asserts that the counterexample is a behavior of the spec: It starts in an
	 * initial state, each step is a step of the next-state relation, and it
	 * either ends in stuttering or loops back to one of its states. Also, the
	 * lasso is fair and violates the property.
	 */
	static void assertValidLasso(final TestMPRecorder recorder) {
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		final List<Object> records = recorder.getRecords(EC.TLC_STATE_PRINT2);
		assertTrue("No counterexample states", records != null && !records.isEmpty());

		final ITool tool = TLCGlobals.mainChecker.tool;
		final TLCState[] trace = new TLCState[records.size()];
		for (int i = 0; i < trace.length; i++) {
			final Object[] objs = (Object[]) records.get(i);
			assertEquals(i + 1, objs[1]);
			trace[i] = ((TLCStateInfo) objs[0]).state;
		}

		final Set<Long> inits = fingerprints(tool.getInitStates());
		assertTrue("Not an initial state: " + trace[0], inits.contains(trace[0].fingerPrint()));
		for (int i = 0; i + 1 < trace.length; i++) {
			assertStep(tool, trace[i], trace[i + 1], i + 1);
		}

		final boolean stutters = recorder.recorded(EC.TLC_STATE_PRINT3);
		final boolean loops = recorder.recorded(EC.TLC_BACK_TO_STATE);
		assertTrue("Counterexample neither stutters nor loops", stutters ^ loops);
		int cyclePos = trace.length - 1;
		if (loops) {
			final Object[] loop = (Object[]) recorder.getRecords(EC.TLC_BACK_TO_STATE).get(0);
			final int back = Integer.parseInt((String) loop[0]);
			assertTrue("Loops back to state " + back + " of " + trace.length, 1 <= back && back <= trace.length);
			assertStep(tool, trace[trace.length - 1], trace[back - 1], trace.length);
			cyclePos = back - 1;
		}
		assertViolates(tool, trace, cyclePos);
	}

	// Evaluates the spec's fairness and the properties on the exact lasso,
	// independently of the SCC search.
	private static void assertViolates(final ITool tool, final TLCState[] trace, final int cyclePos) {
		final List<TLCState> states = Arrays.asList(trace);
		boolean fair = true;
		for (final Action fairness : tool.getTemporals()) {
			fair &= Liveness.astToLive(tool, (ExprNode) fairness.pred, fairness.con).evalOnLasso(tool, states,
					cyclePos, 0);
		}
		assertTrue("Lasso is unfair or satisfies the property",
				fair && !Liveness.findViolatedProperties(tool, states, cyclePos).isEmpty());
	}

	private static void assertStep(final ITool tool, final TLCState from, final TLCState to, final int num) {
		final long fp = to.fingerPrint();
		for (final Action a : tool.getActions()) {
			if (fingerprints(tool.getNextStates(a, from)).contains(fp)) {
				return;
			}
		}
		throw new AssertionError("State " + (num + 1) + " is no successor of state " + num + ": " + from + " -> " + to);
	}

	private static Set<Long> fingerprints(final StateVec states) {
		final Set<Long> fps = new HashSet<>();
		for (int i = 0; i < states.size(); i++) {
			fps.add(states.elementAt(i).fingerPrint());
		}
		return fps;
	}
}
