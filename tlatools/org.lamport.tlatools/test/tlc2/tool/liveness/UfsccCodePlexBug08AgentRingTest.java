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

import org.junit.Test;

import tlc2.output.EC;

/**
 * {@link CodePlexBug08AgentRingTest} with liveness checked by {@link SccStrategy#UFSCC}, whose
 * counterexample may differ from the one asserted by CodePlexBug08AgentRingTest.
 */
public class UfsccCodePlexBug08AgentRingTest extends CodePlexBug08AgentRingTest {

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
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "361", "120"));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "prop_142745588773041000"));
		assertNodeAndPtrSizes(8496L, 2880L);
		UfsccFixture.assertValidLasso(recorder);
	}
}
