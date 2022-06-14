package radix;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

public class RadixSortTest {
	private void _customPrintBucketList(ArrayList<ArrayList<ArrayList<Integer>>> bucketList) {
		for (ArrayList<ArrayList<Integer>> bucket : bucketList) {
			System.out.println("Bucket:");
			for (ArrayList<Integer> bucketContent : bucket) {
				System.out.println("\t" + bucketContent);
			}
		}
	}

	/**
	 * ************************************
	 * Test RadixSort
	 * ************************************
	 */
	int[] testArrayRadix7 = {33, 614, 10216, 2123, 21523, 164504, 5142, 412, 161, 16125, 2231, 2123, 22, 6411, 21, 1123515, 0};
	int[] testArrayIterationRadix7 = {33, 614, 10216, 2123, 21523, 164504, 5142, 402, 6311, 21, 1123515, 0};
	int[] testArrayEquals = {4,4,111,4};
	int[] testArrayPresorted = {0,12,15,234,5562};

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadixSortResult() {
		Exception exCaught = null;
		ArrayList<Integer> result = null;
		try {
			result = RadixSort.sort(testArrayRadix7.clone());
			_customPrintBucketList(RadixSort.getBucketlistSnapshots());
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayRadix7) + "failed because of: " + exCaught);

		Integer[] temp = Arrays.stream(testArrayRadix7).boxed().toArray( Integer[]::new );
		Arrays.sort(temp, Collections.reverseOrder());
		testArrayRadix7 = Arrays.stream(temp).mapToInt(Integer::intValue).toArray();
		
		try {
			for(int i = 0; i< testArrayRadix7.length; i++) {
				assertEquals(testArrayRadix7[i],result.get(i), "RadixSort.sort() failed at index "+i+":\n"+printResult(testArrayRadix7,result));
			}
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayRadix7) + "failed because of: " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadixSortResultOneElement() {
		Exception exCaught = null;
		ArrayList<Integer> result = null;
		try {
			result = RadixSort.sort(new int[]{1});
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array {1} failed because of: " + exCaught);
				
		try {
			assertEquals(1,result.get(0), "RadixSort.sort() with input array {1} failed:\n"+printResult(new int[] {1},result));
			assertEquals(1, result.size(), "RadixSort.sort() with input array {1} failed because of wrong result size: ");
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array {1} failed because of: " + exCaught);
	}
	

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadixSortEqualElements() {
		Exception exCaught = null;
		ArrayList<Integer> result = null;
		try {
			result = RadixSort.sort(testArrayEquals.clone());
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayEquals) + "failed because of: " + exCaught);
		Integer[] temp = Arrays.stream( testArrayEquals ).boxed().toArray( Integer[]::new );
		Arrays.sort(temp, Collections.reverseOrder());
		testArrayEquals = Arrays.stream(temp).mapToInt(Integer::intValue).toArray();

		try {
			for(int i = 0; i<testArrayEquals.length; i++) {
				assertEquals(testArrayEquals[i],result.get(i), "RadixSort.sort() failed at index "+i+":\n"+printResult(testArrayEquals,result));
			}
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayEquals) + "failed because of: " + exCaught);
	
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadixSortPresortedArray() {
		Exception exCaught = null;
		ArrayList<Integer> result = null;
		try {
			result = RadixSort.sort(testArrayPresorted.clone());
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayPresorted) + "failed because of: " + exCaught);
		Integer[] temp = Arrays.stream( testArrayPresorted ).boxed().toArray( Integer[]::new );
		Arrays.sort(temp, Collections.reverseOrder());
		testArrayPresorted = Arrays.stream(temp).mapToInt(Integer::intValue).toArray();
		
		try {
			for(int i = 0; i<testArrayPresorted.length; i++) {
				assertEquals(testArrayPresorted[i],result.get(i), "RadixSort.sort() failed at index "+i+":\n"+printResult(testArrayPresorted,result));
			}
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayPresorted) + "failed because of: " + exCaught);
	
	}
	
	/*
	 * TEST FOR RADIX 7
	 */
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration1() {
		
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration 1";
		
		try {
			/* test intermediate steps: buckets must contain the following keys
			 * Iteration #1
			 */
			// bucket 0
			assertEquals(1, bucketlistSnapshots.get(0).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 1	
			assertEquals(2, bucketlistSnapshots.get(0).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(1).contains(6311), errMsg+" on bucket 1 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			assertTrue(bucketlistSnapshots.get(0).get(1).contains(21), errMsg+" on bucket 1 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 2
			assertEquals(2, bucketlistSnapshots.get(0).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(2).contains(5142), errMsg+" on bucket 2 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			assertTrue(bucketlistSnapshots.get(0).get(2).contains(402), errMsg+" on bucket 2 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 3
			assertEquals(3, bucketlistSnapshots.get(0).get(3).size(), errMsg+" on bucket 3 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(3).contains(33), errMsg+" on bucket 3 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			assertTrue(bucketlistSnapshots.get(0).get(3).contains(2123), errMsg+" on bucket 3 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			assertTrue(bucketlistSnapshots.get(0).get(3).contains(21523), errMsg+" on bucket 3 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 4
			assertEquals(2, bucketlistSnapshots.get(0).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(4).contains(614), errMsg+" on bucket 4 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			assertTrue(bucketlistSnapshots.get(0).get(4).contains(164504), errMsg+" on bucket 4 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 5
			assertEquals(1, bucketlistSnapshots.get(0).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(5).contains(1123515), errMsg+" on bucket 5 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 6
			assertEquals(1, bucketlistSnapshots.get(0).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(0).get(6).contains(10216), errMsg+" on bucket 6 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration2() {
		
		
		final int idxIteration = 1;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #2*/
						 
			// bucket 0
			assertEquals(3, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(402), errMsg+" on bucket 0 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(164504), errMsg+" on bucket 0 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			// bucket 1	
			assertEquals(4, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(6311), errMsg+" on bucket 1 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(614), errMsg+" on bucket 1 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(1123515), errMsg+" on bucket 1 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(10216), errMsg+" on bucket 1 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			// bucket 2
			assertEquals(3, bucketlistSnapshots.get(idxIteration).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(21), errMsg+" on bucket 2 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(2123), errMsg+" on bucket 2 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(21523), errMsg+" on bucket 2 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 2));
				
			// bucket 3
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+" on bucket 3 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(3).contains(33), errMsg+" on bucket 3 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 2));
			
			// bucket 4
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(4).contains(5142), errMsg+" on bucket 4 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 2));
				
			// bucket 5
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			
			// bucket 6
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			

		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration3() {
		
		
		final int idxIteration = 2;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #3*/
			// bucket 0
			assertEquals(3, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21), errMsg+" on bucket 0 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(33), errMsg+" on bucket 0 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 1	
			assertEquals(2, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(2123), errMsg+" on bucket 1 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(5142), errMsg+" on bucket 1 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 2
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(10216), errMsg+" on bucket 2 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 3
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+"on bucket 3 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(3).contains(6311), errMsg+" on bucket 3 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 4
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(4).contains(402), errMsg+" on bucket 4 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 5
			assertEquals(3, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(5).contains(1123515), errMsg+" on bucket 5 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(5).contains(164504), errMsg+" on bucket 5 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(5).contains(21523), errMsg+" on bucket 5 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 3));
			// bucket 6
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(6).contains(614), errMsg+" on bucket 6 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 3));
		
			 
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration4() {
		
		
		final int idxIteration = 3;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #4*/
			// bucket 0
			assertEquals(6, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21), errMsg+" on bucket 0 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(33), errMsg+" on bucket 0 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(10216), errMsg+" on bucket 0 because of missing element 17216!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(402), errMsg+" on bucket 0 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(614), errMsg+" on bucket 0 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 1	
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(21523), errMsg+" on bucket 1 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 2
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(2123), errMsg+" on bucket 2 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 3
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+"on bucket 3 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(3).contains(1123515), errMsg+" on bucket 3 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 4
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(4).contains(164504), errMsg+" on bucket 4 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 5
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(5).contains(5142), errMsg+" on bucket 5 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			// bucket 6
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(6).contains(6311), errMsg+" on bucket 6 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 4));
			
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration5() {
		
		
		final int idxIteration = 4;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #5*/
			// bucket 0
			assertEquals(8, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21), errMsg+" on bucket 0 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(33), errMsg+" on bucket 0 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(402), errMsg+" on bucket 0 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(614), errMsg+" on bucket 0 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(2123), errMsg+" on bucket 0 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(5142), errMsg+" on bucket 0 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(6311), errMsg+" on bucket 0 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			// bucket 1	
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(10216), errMsg+" on bucket 1 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			// bucket 2
			assertEquals(2, bucketlistSnapshots.get(idxIteration).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(21523), errMsg+" on bucket 2 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(2).contains(1123515), errMsg+" on bucket 2 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			// bucket 3
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+"on bucket 3 because of wrong size: ");
			// bucket 4
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			// bucket 5
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			// bucket 6
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(6).contains(164504), errMsg+" on bucket 6 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 5));
			
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration6() {
		final int idxIteration = 5;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #6*/
			// bucket 0
			assertEquals(10, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21), errMsg+" on bucket 0 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(33), errMsg+" on bucket 0 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(402), errMsg+" on bucket 0 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(614), errMsg+" on bucket 0 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(2123), errMsg+" on bucket 0 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(5142), errMsg+" on bucket 0 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(6311), errMsg+" on bucket 0 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(10216), errMsg+" on bucket 0 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21523), errMsg+" on bucket 0 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			// bucket 1	
			assertEquals(2, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(1123515), errMsg+" on bucket 1 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(164504), errMsg+" on bucket 1 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 6));
			// bucket 2
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(2).size(), errMsg+" on bucket 2 because of wrong size: ");
			// bucket 3
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+"on bucket 3 because of wrong size: ");
			// bucket 4
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			// bucket 5
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			// bucket 6
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration7() {
		
		
		final int idxIteration = 6;
		Exception exCaught = null;
		ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = null;
		
		try {
			RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);
		
		try {
			bucketlistSnapshots = RadixSort.getBucketlistSnapshots();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() called after sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		//printBucketlists(bucketlistSnapshots);
		String errMsg = "RadixSort of input array "+printArray(testArrayIterationRadix7) + " failed in iteration "+(idxIteration+1);
		
		try {
			/*Iteration #7*/
			// bucket 0
			assertEquals(11, bucketlistSnapshots.get(idxIteration).get(0).size(), errMsg+" on bucket 0 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(0), errMsg+" on bucket 0 because of missing element 0!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21), errMsg+" on bucket 0 because of missing element 21!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(33), errMsg+" on bucket 0 because of missing element 33!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(402), errMsg+" on bucket 0 because of missing element 402!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(614), errMsg+" on bucket 0 because of missing element 614!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(2123), errMsg+" on bucket 0 because of missing element 2123!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(5142), errMsg+" on bucket 0 because of missing element 5142!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(6311), errMsg+" on bucket 0 because of missing element 6311!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(10216),errMsg+" on bucket 0 because of missing element 10216!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(21523), errMsg+" on bucket 0 because of missing element 21523!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			assertTrue(bucketlistSnapshots.get(idxIteration).get(0).contains(164504), errMsg+" on bucket 0 because of missing element 164504!"+ printBucketlistIteration(bucketlistSnapshots, 7));
			// bucket 1	
			assertEquals(1, bucketlistSnapshots.get(idxIteration).get(1).size(), errMsg+" on bucket 1 because of wrong size: ");
			assertTrue(bucketlistSnapshots.get(idxIteration).get(1).contains(1123515), errMsg+" on bucket 1 because of missing element 1123515!"+ printBucketlistIteration(bucketlistSnapshots, 1));
			// bucket 2
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(2).size(),errMsg+" on bucket 2 because of wrong size: ");
			// bucket 3
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(3).size(), errMsg+"on bucket 3 because of wrong size: ");
			// bucket 4
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(4).size(), errMsg+" on bucket 4 because of wrong size: ");
			// bucket 5
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(5).size(), errMsg+" on bucket 5 because of wrong size: ");
			// bucket 6
			assertEquals(0, bucketlistSnapshots.get(idxIteration).get(6).size(), errMsg+" on bucket 6 because of wrong size: ");
			
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRadix7SortBucketlistsIteration7Result() {
		Exception exCaught = null;

		ArrayList<Integer> result = null;
		try {
			result = RadixSort.sort(testArrayIterationRadix7.clone());
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " failed because of: " + exCaught);

		assertNotNull(result, "RadixSort.sort() with input array " + printArray(testArrayIterationRadix7) + " did not return a valid result in form of an ArrayList.");

		try {
			String errMsg = "Result of RadixSort.sort() with input array "+printArray(testArrayIterationRadix7);

			Integer[] temp = Arrays.stream(testArrayIterationRadix7).boxed().toArray( Integer[]::new );
			Arrays.sort(temp, Collections.reverseOrder());
			int[] expectedResult = Arrays.stream(temp).mapToInt(Integer::intValue).toArray();

			assertEquals(12, result.size(), errMsg+" has the wrong size.");

			assertEquals(0, result.get(11), errMsg+" is wrong at index 11!"+ printResult(expectedResult, result));
			assertEquals(21, result.get(10), errMsg+" is wrong at index 10!"+ printResult(expectedResult, result));
			assertEquals(33, result.get(9), errMsg+" is wrong at index 9!"+ printResult(expectedResult, result));
			assertEquals(402, result.get(8), errMsg+" is wrong at index 8!"+ printResult(expectedResult, result));
			assertEquals(614, result.get(7), errMsg+" is wrong at index 7 !"+ printResult(expectedResult, result));
			assertEquals(2123, result.get(6), errMsg+" is wrong at index 6!"+ printResult(expectedResult, result));
			assertEquals(5142, result.get(5), errMsg+" is wrong at index 5!"+ printResult(expectedResult, result));
			assertEquals(6311, result.get(4), errMsg+" is wrong at index 4!"+ printResult(expectedResult, result));
			assertEquals(10216, result.get(3),errMsg+" is wrong at index 3!"+ printResult(expectedResult, result));
			assertEquals(21523, result.get(2), errMsg+" is wrong at index 2!"+ printResult(expectedResult, result));
			assertEquals(164504, result.get(1), errMsg+" is wrong at index 1!"+ printResult(expectedResult, result));
			assertEquals(1123515, result.get(0), errMsg+" is wrong at index 0!"+ printResult(expectedResult, result));


		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "RadixSort.getBucketlistSnapshots() could not be tested because of " + exCaught);
	}
	
	
	@Test
	public void testRunTime() {
		int numberCount = 1000;
		int[] prior = new int[numberCount];
		for(int i = 0; i<numberCount; i++) {
			prior[i] = Integer.parseInt(Integer.toString(Integer.parseInt(Integer.valueOf((int)(1000000*Math.random())).toString(), 10),7));//Integer.valueOf((int)(1000000*Math.random()));
		}

		/*assertTimeoutPreemptively(Duration.ofMillis(1000), () -> {
			RadixSort.sort(prior);
	    });*/
		long s = System.currentTimeMillis();
		RadixSort.sort(prior);
		long e = System.currentTimeMillis();
		System.out.println("Numbers: "+numberCount+"; Time: "+(e-s)+";");
		
		
		numberCount = 100000;
		prior = new int[numberCount];
		for(int i = 0; i<numberCount; i++) prior[i] = Integer.parseInt(Integer.toString(Integer.parseInt(Integer.valueOf((int)(1000000*Math.random())).toString(), 10),7));//Integer.valueOf((int)(1000000*Math.random()));
		
		s = System.currentTimeMillis();
		RadixSort.sort(prior);
		e = System.currentTimeMillis();
		System.out.println("Numbers: "+numberCount+"; Time: "+(e-s)+";");		
	}
	
	private void printArrayBucketlists(ArrayList<ArrayList<Integer>[]> list) {
		for(int i = 0; i < list.size(); i++) {
			System.out.println("\nIteration #"+(i+1));
			
			ArrayList<Integer>[] tmp = list.get(i);
			
			
			// get size of the largest bucket
			int maxSize = 0;
			for(int j = 0; j < tmp.length; j++) {
				if(tmp[j].size() > maxSize) maxSize = tmp[j].size();
			}
			
			// print header
			System.out.print("Bucket:");
			for(int j = 0; j< tmp.length;j++) {
				System.out.printf("\t%d",j);
			}
			System.out.print("\n----------------------------------------------------------------------------------------\n");
			
			for(int j = 0; j < maxSize; j++) {
				
				// line by line over all buckets (all first entries, all second entries,....)
				for(int k = 0; k < tmp.length; k++) {
					if(j < tmp[k].size())
						System.out.print("\t"+tmp[k].get(j));
					else System.out.print("\t");
				}
				System.out.println();
			}
		}
	}
	
	private void printBucketlists(ArrayList<ArrayList<ArrayList<Integer>>> list) {
		for(int i = 0; i < list.size(); i++) {
			System.out.println("\nIteration #"+(i+1));
			
			ArrayList<ArrayList<Integer>> tmp = list.get(i);
			
			
			// get size of the largest bucket
			int maxSize = 0;
			for(int j = 0; j < tmp.size(); j++) {
				if(tmp.get(j).size() > maxSize) maxSize = tmp.get(j).size();
			}
			
			// print header
			System.out.print("Bucket:");
			for(int j = 0; j< tmp.size();j++) {
				System.out.printf("\t%d",j);
			}
			System.out.print("\n----------------------------------------------------------------------------------------\n\t");
			
			for(int j = 0; j < maxSize; j++) {
				
				// line by line over all buckets (all first entries, all second entries,....)
				for(int k = 0; k < tmp.size(); k++) {
					if(j < tmp.get(k).size())
						System.out.print("\t"+tmp.get(k).get(j));
					else System.out.print("\t");
				}
				System.out.println();System.out.print("\t");
			}
		}
	}
	
	private String printBucketlistIteration(ArrayList<ArrayList<ArrayList<Integer>>> list, int iteration) {
		StringBuilder sb = new StringBuilder();
		sb.append("\n\tIteration #").append(iteration).append(" (of your bucketlist)\n");
		
		if(list.get(iteration-1).size() < iteration)
			return "Couldn't get bucketlist of iteration "+iteration+" as list of bucketlists has only size "+list.size()+"!";
		ArrayList<ArrayList<Integer>> tmp = list.get(iteration-1);
		
		
		// get size of the largest bucket
		int maxSize = 0;
		for(int j = 0; j < tmp.size(); j++) {
			if(tmp.get(j).size() > maxSize) maxSize = tmp.get(j).size();
		}
		
		// print header
		sb.append("\tBucket:");
		for(int j = 0; j< tmp.size();j++) {
			sb.append(String.format("\t\t%d",j));
		}
		sb.append("\n\t----------------------------------------------------------------------------------------\n\t\t\t");
		
		for(int j = 0; j < maxSize; j++) {
			
			// line by line over all buckets (all first entries, all second entries,....)
			for(int k = 0; k < tmp.size(); k++) {
				if(j < tmp.get(k).size())
					sb.append("\t").append(tmp.get(k).get(j));
				else sb.append("\t");
			}
			sb.append("\n\t\t\t");
		}
		return sb.toString();
	}
	
	private String printArray(int[] arr) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		
		for(Integer i : arr) {
			sb.append(i).append(",");
		}
		
		if(sb.length()>0) sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",")+1, "}");
		return sb.toString();
	}
	
	private String printResult(int[] arrExpected, ArrayList<Integer> arrCurrent) {
		 StringBuilder sb = new StringBuilder();
		 final String strIndent = "     ";
		 int maxLength = Math.max(arrExpected.length, arrCurrent.size());
		 
		 sb.append(strIndent+"index   \t");
		 for(int i = 0; i < maxLength;++i) {
			 sb.append(String.format("%02d\t", i));
		 }
		 sb.append("\n"+strIndent+"----------");
		 // add horizontal line
		 for(int i = 0; i < maxLength;++i) {
			 sb.append("--------");
		 }
		 
		 
		 // add heap array
		 sb.append("\n"+strIndent+"your array\t");
		 for(int i = 0; i < arrCurrent.size();++i) {
			 if(arrCurrent.get(i) != null)
				 sb.append(String.format("%2d\t", arrCurrent.get(i)));
			 else
				 sb.append("Null\t");
		 }
			 
		 // add expected heap array
		 sb.append("\n"+strIndent+"expected\t");
		 for(int i = 0; i < arrExpected.length;++i) {
			 sb.append(String.format("%2d\t", arrExpected[i]));
		 }
		 
		 sb.append("\n"+strIndent+"-->");
		 return sb.toString();
	}
}
