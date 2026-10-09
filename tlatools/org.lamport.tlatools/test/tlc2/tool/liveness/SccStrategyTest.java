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

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import tlc2.TLCGlobals;

public class SccStrategyTest {

	private String oldLnCheck;
	private int oldWorkers;

	@Before
	public void before() {
		oldLnCheck = TLCGlobals.lnCheck;
		oldWorkers = TLCGlobals.getNumWorkers();
		System.clearProperty(SccStrategy.PROPERTY);
		System.clearProperty(SccStrategy.WORKERS_PROPERTY);
	}

	@After
	public void after() {
		TLCGlobals.lnCheck = oldLnCheck;
		TLCGlobals.setNumWorkers(oldWorkers);
		System.clearProperty(SccStrategy.PROPERTY);
		System.clearProperty(SccStrategy.WORKERS_PROPERTY);
	}

	@Test
	public void testPropertyNames() {
		assertEquals("tlc2.tool.liveness.LiveCheck.scc", SccStrategy.PROPERTY);
		assertEquals("tlc2.tool.liveness.LiveCheck.sccWorkers", SccStrategy.WORKERS_PROPERTY);
	}

	@Test
	public void testDefaultIsTarjan() {
		assertEquals(SccStrategy.TARJAN, SccStrategy.current());
	}

	@Test
	public void testPipeline() {
		System.setProperty(SccStrategy.PROPERTY, "pipeline");
		assertEquals(SccStrategy.PIPELINE, SccStrategy.current());
	}

	@Test
	public void testUfscc() {
		System.setProperty(SccStrategy.PROPERTY, "ufscc");
		assertEquals(SccStrategy.UFSCC, SccStrategy.current());
	}

	@Test
	public void testSequentialLivenessForcesTarjanOverUfscc() {
		System.setProperty(SccStrategy.PROPERTY, "ufscc");
		TLCGlobals.lnCheck = "seq";
		assertEquals(SccStrategy.TARJAN, SccStrategy.current());
	}

	@Test
	public void testCaseAndWhitespaceInsensitive() {
		System.setProperty(SccStrategy.PROPERTY, " PipeLine ");
		assertEquals(SccStrategy.PIPELINE, SccStrategy.current());
		System.setProperty(SccStrategy.PROPERTY, "Tarjan");
		assertEquals(SccStrategy.TARJAN, SccStrategy.current());
	}

	@Test
	public void testInvalidValueIsRejected() {
		System.setProperty(SccStrategy.PROPERTY, "bogus");
		try {
			SccStrategy.current();
			fail("Expected IllegalArgumentException");
		} catch (IllegalArgumentException e) {
			assertTrue(e.getMessage(), e.getMessage().contains("bogus"));
			assertTrue(e.getMessage(), e.getMessage().contains(SccStrategy.PROPERTY));
			assertTrue(e.getMessage(), e.getMessage().contains("tarjan"));
			assertTrue(e.getMessage(), e.getMessage().contains("pipeline"));
		}
	}

	@Test
	public void testSequentialLivenessForcesTarjan() {
		System.setProperty(SccStrategy.PROPERTY, "pipeline");
		TLCGlobals.lnCheck = "seq";
		assertEquals(SccStrategy.TARJAN, SccStrategy.current());
		TLCGlobals.lnCheck = "seqfinal";
		assertEquals(SccStrategy.TARJAN, SccStrategy.current());
	}

	@Test
	public void testWorkersDefaultToTLCWorkers() {
		TLCGlobals.setNumWorkers(3);
		assertEquals(3, SccStrategy.workers());
	}

	@Test
	public void testWorkersFromProperty() {
		TLCGlobals.setNumWorkers(3);
		System.setProperty(SccStrategy.WORKERS_PROPERTY, "7");
		assertEquals(7, SccStrategy.workers());
	}

	@Test
	public void testWorkersAtLeastOne() {
		System.setProperty(SccStrategy.WORKERS_PROPERTY, "0");
		assertEquals(1, SccStrategy.workers());
		System.setProperty(SccStrategy.WORKERS_PROPERTY, "-4");
		assertEquals(1, SccStrategy.workers());
	}
}
