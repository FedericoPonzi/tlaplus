/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static tlc2.tool.fp.DiskFPSet.MARK_FLUSHED;
import static tlc2.tool.fp.OffHeapDiskFPSet.EMPTY;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.rmi.RemoteException;
import java.util.Arrays;
import java.util.Random;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;

public class OffHeapDiskFPSetTest {
	
	protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "OffHeapDiskFPSetTest"
			+ System.currentTimeMillis();
	protected static final String filename = "OffHeapDiskFPSetTest";

//	@Test
//	public void testInsertAndEvictRnd() throws Exception {
//		Random rnd = new Random();
//		for (int i = 0; i < 1000; i++) {
//			doTest(System.currentTimeMillis(), rnd.nextInt(255) + 1);
//		}
//	}
	
	@Test
	public void testInsertAndEvict1() throws Exception {
		doTest(1473793977852L, 87);
	}
	
	@Test
	public void testInsertAndEvict2() throws Exception {
		doTest(1473793976137L, 87);
	}
	
	@Test
	public void testInsertAndEvict3() throws Exception {
		doTest(1473839150698L, 46);
	}
	
	@Test
	public void testInsertAndEvict4() throws Exception {
		doTest(1473839150698L, 46);
	}
	
	@Test
	public void testInsertAndEvict5() throws Exception {
		doTest(1473839322351L, 23);
	}

	@Test
	public void testInsertAndEvict6() throws Exception {
		doTest(1473839380539L, 23);
	}

	@Test
	public void testInsertAndEvict7() throws Exception {
		doTest(1473839422899L, 11);
	}

	@Test
	public void testInsertAndEvict8() throws Exception {
		doTest(1473839543883L, 11);
	}
	
	@Test
	public void testInsertAndEvict9() throws Exception {
		doTest(1473871461079L, 64);
	}

	@Test
	public void testInsertAndEvict10() throws Exception {
		doTest(1473871462765L, 64);
	}

	@Test
	public void testInsertAndEvict11() throws Exception {
		doTest(1473871522834L, 32);
	}
	
	@Test
	public void testInsertAndEvict12() throws Exception {
		doTest(1473871526136L, 32);
	}

	@Test
	public void testInsertAndEvict13() throws Exception {
		doTest(1473873732723L, 47);
	}

	@Test
	public void testInsertAndEvict14() throws Exception {
		doTest(1473871294851L, 93);
	}

	@Test
	public void testInsertAndEvict15() throws Exception {
		doTest(1473871365625L, 93);
	}

	@Test
	public void testInsertAndEvict16() throws Exception {
		doTest(1473871209569L, 157);
	}

	private void doTest(final long rgenseed, final long length) throws RemoteException, IOException, NoSuchFieldException, IllegalAccessException {
		new File(tmpdir).mkdirs();
		
		final DummyFPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemoryInFingerprintCnt(length);
		
		final DiskFPSet fpSet = new OffHeapDiskFPSet(fpSetConfig);
		fpSet.init(1, tmpdir, filename);

		// Insert n randomly choosen positive longs.
		Random random = new Random(rgenseed);
		for (int i = 0; i < length / 2; i++) {
			assertFalse(fpSet.put(getFingerprint(random)));
		}

		// Get the current content of LongArray for later comparison of special elements.
		Field field = OffHeapDiskFPSet.class.getDeclaredField("array");
		field.setAccessible(true);
		final long[] expected = LongArrays.toArray((LongArray) field.get(fpSet));
		
		// Flush/Evict the first time and assure its successful.
		assertTrue(fpSet.getGrowDiskMark() == 0);
		fpSet.forceFlush();
		fpSet.contains(1L); // contains triggers eviction
		assertTrue(fpSet.getGrowDiskMark() == 1);
		
		// Special elements (EMPTY or marked evicted) do not change positions
		// when sorted.
		final LongArray actual = (LongArray) field.get(fpSet);
		for (int i = 0; i < expected.length; i++) {
			if (expected[i] == EMPTY) {
				assertEquals(
						String.format(
								"Expected empty position with seed %sL and length %s.\n\nexpected: %s\n\nactual: %s",
								new Object[] { rgenseed, length, Arrays.toString(expected), actual.toString() }),
						EMPTY, actual.get(i));
			} else if (expected[i] < EMPTY) {
				assertEquals(
						String.format(
								"Expected negative position with seed %sL and length %s.\n\nexpected: %s\n\nactual: %s",
								new Object[] { rgenseed, length, Arrays.toString(expected), actual.toString() }),
						EMPTY, actual.get(i));
			}
		}
		
		random = new Random(rgenseed);
		for (int i = 0; i < length / 2; i++) {
			final long fp = getFingerprint(random);
			assertTrue(String.format("Failed to find fp %s/%s with seed %sL and length %s.\n\nexpected: %s\n\nactual: %s",
					new Object[] { fp, (fp | MARK_FLUSHED), rgenseed, length, Arrays.toString(expected),
							actual.toString() }),
					fpSet.contains(fp));
		}
		
		assertTrue(
				String.format("Invariant violated with seed %sL and length %s.\n\nexpected: %s\n\nactual: %s",
						new Object[] { rgenseed, length, Arrays.toString(expected), actual.toString() }),
				fpSet.checkInvariant());

		// Clear the index to secondary/disk which hides secondary from
		// DiskFPSet.
		field = DiskFPSet.class.getDeclaredField("index");
		field.setAccessible(true);
		field.set(fpSet, null);

		// Confirm that even without secondary, it's possible to lookup the
		// fingerprints.
		random = new Random(rgenseed);
		for (int i = 0; i < length / 2; i++) {
			final long fp = getFingerprint(random);
			assertTrue(String.format("Failed to find fp %s/%s with seed %sL and length %s.\n\nexpected: %s\n\nactual: %s",
					new Object[] { fp, (fp | MARK_FLUSHED), rgenseed, length, Arrays.toString(expected),
							actual.toString() }),
					fpSet.contains(fp));
		}
		
		fpSet.close();
	}
	
	@Test
	public void testOffset1Page() throws IOException, NoSuchMethodException, SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		final long length = DiskFPSet.NumEntriesPerPage;
		doTestOffset(length, 1474536306841L);
	}
	
	@Test
	public void testOffset3Page() throws IOException, NoSuchMethodException, SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		long length = DiskFPSet.NumEntriesPerPage * 3L;
		doTestOffset(length, 1474536306841L);
	}
	
	@Test
	public void testOffset5Page() throws IOException, NoSuchMethodException, SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		long length = DiskFPSet.NumEntriesPerPage * 5L;
		doTestOffset(length, 1474536306841L);
	}
	
	@Test
	public void testOffset9Page() throws IOException, NoSuchMethodException, SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		long length = DiskFPSet.NumEntriesPerPage * 9L;
		doTestOffset(length, 1474536306841L);
	}

	private void doTestOffset(long length, long rgenseed) throws RemoteException, IOException, NoSuchMethodException,
			IllegalAccessException, InvocationTargetException {
		new File(tmpdir).mkdirs();
		
		final DummyFPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemoryInFingerprintCnt(length);
		
		final OffHeapDiskFPSet fpSet = new OffHeapDiskFPSet(fpSetConfig);
		fpSet.init(1, tmpdir, filename);

		final SortedSet<Long> longs = new TreeSet<Long>();
		
		// Insert n randomly choosen positive longs.
		Random random = new Random(rgenseed);
		for (int i = 0; i < length / 2; i++) {
			long fingerprint = getFingerprint(random);
			assertFalse(fpSet.put(fingerprint));
			longs.add(fingerprint);
		}
		fpSet.forceFlush();
		long fingerprint = getFingerprint(random);
		assertFalse(fpSet.put(fingerprint));
		
		final Method field = OffHeapDiskFPSet.class.getDeclaredMethod("getOffset", new Class[] {int.class, long.class});
		field.setAccessible(true);
		
		for (long i = 0L; i < longs.size(); i++) {
			long fp = longs.first();
			assertEquals(String.format("Length: %s with seed: %s", length, rgenseed), i , field.invoke(fpSet, 0, fp));
			longs.remove(fp);
		}
	}

	private static long getFingerprint(Random random) {
		final long fp = (((long) random.nextInt(Integer.MAX_VALUE - 1) + 1) << 32) | (random.nextInt() & 0xffffffffL);
		return fp;
	}
}