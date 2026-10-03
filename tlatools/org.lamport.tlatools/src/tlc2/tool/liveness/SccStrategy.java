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

import java.util.Arrays;
import java.util.Locale;
import java.util.stream.Collectors;

import tlc2.TLCGlobals;

/**
 * Selects how {@link LiveWorker} searches and checks the strongly connected
 * components (SCC) of a single liveness graph.
 * <p>
 * Set with <code>-Dtlc2.tool.liveness.LiveCheck.scc=&lt;name&gt;</code>
 * (experimental, default <code>tarjan</code>).
 */
public enum SccStrategy {
	/**
	 * Tarjan's sequential SCC search; each SCC is checked by the searching
	 * thread before the search continues.
	 */
	TARJAN,
	/**
	 * Tarjan's sequential SCC search, but the SCCs it finds are checked
	 * concurrently by a pool of {@link #workers()} threads while the search
	 * continues. Large SCCs are split among the threads. The counterexample
	 * reported is the same one {@link #TARJAN} reports.
	 */
	PIPELINE;

	public static final String PROPERTY = LiveCheck.class.getName() + ".scc";

	public static final String WORKERS_PROPERTY = LiveCheck.class.getName() + ".sccWorkers";

	/**
	 * @return The strategy selected by {@link #PROPERTY}. Sequential liveness
	 *         checking (<code>-lncheck seq...</code>) always uses
	 *         {@link #TARJAN}.
	 * @throws IllegalArgumentException if the property has an unknown value.
	 */
	public static SccStrategy current() {
		final String value = System.getProperty(PROPERTY, TARJAN.toString()).trim();
		final SccStrategy strategy;
		try {
			strategy = valueOf(value.toUpperCase(Locale.ROOT));
		} catch (IllegalArgumentException e) {
			throw new IllegalArgumentException(String.format("Unknown value '%s' for -D%s; expected one of: %s.",
					value, PROPERTY,
					Arrays.stream(values()).map(SccStrategy::toString).collect(Collectors.joining(", "))));
		}
		return TLCGlobals.doSequentialLiveness() ? TARJAN : strategy;
	}

	/**
	 * @return The number of threads that check SCCs concurrently (at least one).
	 *         Defaults to the number of TLC workers.
	 */
	public static int workers() {
		return Math.max(1, Integer.getInteger(WORKERS_PROPERTY, TLCGlobals.getNumWorkers()));
	}

	@Override
	public String toString() {
		return name().toLowerCase(Locale.ROOT);
	}
}
