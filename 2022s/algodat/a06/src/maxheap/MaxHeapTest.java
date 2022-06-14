package maxheap;

import static org.junit.jupiter.api.Assertions.*;

import java.util.Arrays;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

public class MaxHeapTest {
	/**
	 * ************************************
	 * Test In-Place HeapSort based on MaxHeap implementation
	 * 
	 * ************************************
	 */
    private final int[] heap0 = {0};
    private final int[] heap012 = {0,1,2};
    private final int[] heap102 = {1,0,2};
    private final int[] heap102solution1 = {0,1,2};
    private final int[] heap102solution2 = {0,2,1};
    private final int[] heap43210 = {4,3,2,1,0};
	private final int[] testArray = {3, 9, 17, 2, 23, 1, 5, 4, 19, 17, 7, 18, 8, 67, 6, 11, 0};
	private final int[] testMaxHeapArraySorted = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 17, 17, 18, 19, 23, 67};
	private final int[] testMinHeapArraySorted = {67,23,19,18,17,17,11,9,8,7,6,5,4,3,2,1,0};
	private final int[] testArray2 = {6,5,6,15,4,7,20,16};
	private final int[] testArray3 = {3,9,5,4,0};
	MaxHeap heap;
	

   @Test
   @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
   public void testHeapBottomUpWithArrOneElement() {
	   Exception exCaught = null;
	   
       try{
           heap = new MaxHeap(heap0);
       } catch (Exception ex) {
    	   exCaught = ex;
       }
       assertTrue(exCaught == null, "Heap with input array {0} could not be created because of: "+exCaught);
       
       try {
    	   int[] heapArr = heap.getHeap();
    	   assertEquals(heap0[0], heapArr[0], "BottomUp construction of heap with input array {0} failed: ");
    	   assertEquals(1, heap.size(), "BottomUp construction of heap with input array {0} has wrong size: ");
       } catch (Exception ex) {
    	   exCaught = ex;
       }
       assertTrue(exCaught == null, "Heap with input array {0} could not be tested because of: "+exCaught);
    }
	   
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpWithArrWithoutDownheap() {
		Exception exCaught = null;
		   
	    try{
	    	heap = new MaxHeap(heap012);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught == null, "Heap with input array "+printArray(heap012)+" could not be created because of: "+exCaught);
        
	    try {
	    	String errMsg = "BottomUp construction of heap with input array "+printArray(heap012);
	    	int[] heapArr = heap.getHeap();
	    	
	    	assertEquals(heap012.length, heap.size(), errMsg+" returned wrong heap size: ");
	    	
	    	for(int i = 0; i < heap012.length; i++)
	    		assertEquals(heap012[i], heapArr[i], errMsg+" has wrong element at index "+i);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught == null, "Heap with input array "+printArray(heap012)+" could not be tested because of: "+exCaught);
    }
	
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpWithArrWithSingleDownheap() {
		Exception exCaught = null;
		   
	    try{
	    	heap = new MaxHeap(heap102);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
		assertNull(exCaught, "Heap with input array " + printArray(heap102) + " could not be created because of: " + exCaught);
      
        try {
        	
        	int[] heapArr = getHeapArray(heap);
        	boolean result = false;

        	Set<Object> currentSet  = setOf(Arrays.stream(heapArr).boxed().toArray( Integer[]::new ));
            Set<Object> expectedSet1= setOf(Arrays.stream(heap102solution1).boxed().toArray( Integer[]::new ));
            Set<Object> expectedSet2= setOf(Arrays.stream(heap102solution2).boxed().toArray( Integer[]::new ));
            
        	if(currentSet.equals(expectedSet1) || currentSet.equals(expectedSet2))
        		result = true;
        	
        	assertTrue(result, "Heap with input array "+printArray(heap102)+" was not created correctly.");
                	
        }catch(Exception ex) {
        	exCaught = ex;
        }
        assertTrue(exCaught == null, "Heap with input array "+printArray(heap102)+" could not be tested because of: "+exCaught);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpWithArrWithMultipleDownheap() {
    	Exception exCaught = null;
		   
	    try{
	    	heap = new MaxHeap(heap43210);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue( exCaught == null, "Heap with input array "+printArray(heap43210)+" could not be created because of: "+exCaught);
      
	    try {
	    	assertEquals(heap43210.length, heap.size(), "BottomUp construction with input array "+printArray(heap43210)+" failed because of wrong size: ");
	    	assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "BottomUp construction with input array "+printArray(heap43210)+" failed:\n"+printHeapArray(getHeapArray(heap)));
	    	
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught == null, "Heap with input array "+printArray(heap43210)+" could not be tested because of: "+exCaught);
    }
	
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpInitWithNull() {
    	Exception exCaught = null;
		   
	    try{
	    	heap = new MaxHeap(null);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught instanceof IllegalArgumentException, "Heap created with null as argument didn't throw an IllegalArgumentException.");
    }
    
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapBottomUpConstructionLarge() {		
		Exception exCaught = null;
		   
	    try{
	    	heap = new MaxHeap(testArray);
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught == null, "Heap with input array "+printArray(testArray)+" could not be created because of: "+exCaught);
		
	    try {
	    	//int[] heapArr = heap.getHeap(); //[0, 2, 1, 3, 7, 8, 5, 4, 19, 17, 23, 18, 17, 67, 6, 11, 9]
	    	assertEquals(testArray.length, heap.size(), "BottomUp construction with input array "+printArray(testArray)+" failed because of wrong size: ");
	    	assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "BottomUp construction with input array "+printArray(testArray)+" failed:\n"+printHeapArray(getHeapArray(heap)));
	    } catch (Exception ex) {
	    	exCaught = ex;
	    }
	    assertTrue(exCaught == null, "Heap with input array "+printArray(testArray)+" could not be tested because of: "+exCaught);
	}
	
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpRemoveMaxLastElement() {
    	Exception exCaught = null;
       	MaxHeap heap = null;
       	
       	try {
       		heap = new MaxHeap(heap0);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught == null, "heap.removeMax() failed because heap could not be created: ");
       	
       	// check removeMax() return value
       	try {
       		assertEquals(0,heap.removeMax(), "heap.removeMax() returned wrong result on heap with input sequence "+printArray(heap0)+": ");
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught==null, "heap.removeMax() on heap with one element only failed because of: "+exCaught);
       	
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpRemoveMaxWithoutDownheap() {
    	Exception exCaught = null;
       	MaxHeap heap = null;
       	
       	try {
       		heap = new MaxHeap(heap012);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught == null, "heap.removeMax() failed because heap could not be created: ");
       	
        try {
        	assertEquals(heap012.length, heap.size(), "heap.removeMax() and input array "+printArray(heap012)+" failed because of wrong size: ");
	    	assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "heap.removeMax() and input array "+printArray(heap012)+" failed:\n"+printHeapArray(getHeapArray(heap)));
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heap.removeMax() failed because your heap couldn't be analyzed because of: "+exCaught);
    	
    	// check removeMax() return value
    	try {
    		assertEquals(2,heap.removeMax(), "heap.removeMax() returned wrong result on heap with input array "+printArray(heap012)+": ");
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heap.removeMax() failed when calling removeMax() on heap with input array "+printArray(heap012)+" because of: "+exCaught);
    	
    	// check remaining heap
    	try {
           	assertEquals(heap012.length-1, heap.size(), "heap.removeMax() and input array "+printArray(heap012)+" + calling removeMax() failed because of wrong size: ");
    	   	assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "heap.removeMax() and input array "+printArray(heap012)+" + calling removeMax() failed:\n"+printHeapArray(getHeapArray(heap)));
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heapPQ.removeMax() failed as your heap couldn't be analyzed because of: "+exCaught);
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapBottomUpRemoveMaxWithDownheap() {
    	Exception exCaught = null;
              	
       	try {
       		heap = new MaxHeap(heap43210);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught == null, "heap.removeMax() failed because heap could not be created: ");
       	
       	try {
          	assertEquals(heap43210.length, heap.size(), "heap.removeMax() and input array "+printArray(heap43210)+" failed because of wrong size: ");
    	    assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "heap.removeMax() and input array "+printArray(heap43210)+" failed:\n"+printHeapArray(getHeapArray(heap)));
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heap.removeMax() failed because your heap with input array "+printArray(heap43210)+" couldn't be analyzed because of: "+exCaught);
    	
    	// check removeMax() return value
    	try {
    		assertEquals(4,heap.removeMax(), "heap.removeMax() returned wrong result on heap with input array "+printArray(heap43210)+": ");
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heapPQ.removeMax() failed when calling removeMax() on heap with input array "+printArray(heap43210)+" caused: "+exCaught);
    	
    	// check remaining heap
    	try {
    		assertEquals(heap43210.length-1, heap.size(), "heap.removeMax() and input array "+printArray(heap43210)+" + calling removeMax() failed because of wrong size: ");
    	    assertTrue(testMaxHeapStructure(getHeapArray(heap),0), "heap.removeMax() and input array "+printArray(heap43210)+" + calling removeMax() failed:\n"+printHeapArray(getHeapArray(heap)));
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
    	assertTrue(exCaught==null, "heap.removeMax() failed as your heap with input array "+printArray(heap43210)+" and after 1x removeMax() couldn't be analyzed because of: "+exCaught);
    }
	
		
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapBottomUpContainsExisting() {
		Exception exCaught = null;
      	
       	try {
       		heap = new MaxHeap(testArray);		// {3, 9, 17, 2, 23, 1, 5, 4, 19, 17, 7, 18, 8, 67, 6, 11, 0};
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught == null, "heap.contains() failed because heap could not be created: ");
       
		try {
			final String errMsg = "heap.contains() and input array "+printArray(testArray) +" returned FALSE for element: ";
			assertTrue(heap.contains(3), errMsg+"3");
			assertTrue(heap.contains(9), errMsg+"9");
			assertTrue(heap.contains(17), errMsg+"17");
			assertTrue(heap.contains(2), errMsg+"2");
			assertTrue(heap.contains(23), errMsg+"23");
			assertTrue(heap.contains(1), errMsg+"1");
			assertTrue(heap.contains(5), errMsg+"5");
			assertTrue(heap.contains(4), errMsg+"4");
			assertTrue(heap.contains(19), errMsg+"19");
			assertTrue(heap.contains(17), errMsg+"17");
			assertTrue(heap.contains(7), errMsg+"7");
			assertTrue(heap.contains(18), errMsg+"18");
			assertTrue(heap.contains(8), errMsg+"8");
			assertTrue(heap.contains(67), errMsg+"67");
			assertTrue(heap.contains(6), errMsg+"6");
			assertTrue(heap.contains(11), errMsg+"11");
			assertTrue(heap.contains(0), errMsg+"0");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught == null, "heap.contains() could not be tested because of: "+exCaught);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapBottomUpContainsNotExisting() {
		Exception exCaught = null;
      	
       	try {
       		heap = new MaxHeap(testArray);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
       	assertTrue(exCaught == null, "heap.contains() failed because heap could not be created: ");
       
		try {
			final String errMsg = "heap.contains() and input array "+printArray(testArray) +" returned TRUE for element: ";
			assertFalse(heap.contains(44), errMsg+"44");
			assertFalse(heap.contains(-1), errMsg+"-1");
			assertFalse(heap.contains(10), errMsg+"10");
			assertFalse(heap.contains(13), errMsg+"13");
			assertFalse(heap.contains(102), errMsg+"102");
			assertFalse(heap.contains(3489), errMsg+"3489");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught == null, "heap.contains() could not be tested because of: "+exCaught);
	}
		
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapBottomUpSort() {
		Exception exCaught = null;
      	int[] tmp = testArray.clone();
       	
		try {
			MaxHeap.sort(tmp);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught == null, "heap.sort() failed because of: "+exCaught);
		
		try {
			for(int i = 0; i < testMaxHeapArraySorted.length; i++) {
				assertEquals(testMaxHeapArraySorted[i], tmp[i], "heap.sort() with input array "+printArray(testArray)+" failed at index "+i+printHeapArray(testMaxHeapArraySorted,tmp));
			}
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertTrue(exCaught == null, "heap.sort() failed because of: "+exCaught);
	}

	@Test
	@Timeout(value = 2000, unit = TimeUnit.MILLISECONDS)
	public void testHeapBottomUpRunTime() {
		int numberCount = 1000;
		int[] prior = new int[numberCount];
		for(int i = 0; i<numberCount; i++) prior[i] = (Double.valueOf(Math.random()).intValue());
		
		long s = System.currentTimeMillis();
		heap = new MaxHeap(prior);
		long e = System.currentTimeMillis();
		System.out.println("Numbers: "+numberCount+"; Time: "+(e-s)+";");
				
		
		
		numberCount = 100000;
		prior = new int[numberCount];
		for(int i = 0; i<numberCount; i++) prior[i] = Double.valueOf(Math.random()).intValue();
		
		s = System.currentTimeMillis();
		heap = new MaxHeap(prior);
		e = System.currentTimeMillis();
		System.out.println("Numbers: "+numberCount+"; Time: "+(e-s)+";");		
			
		
		
		numberCount = 10000000;
		prior = new int[numberCount];
		for(int i = 0; i<numberCount; i++) prior[i] = Double.valueOf(Math.random()).intValue();
		
		s = System.currentTimeMillis();
		heap = new MaxHeap(prior);
		e = System.currentTimeMillis();
		System.out.println("Numbers: "+numberCount+"; Time: "+(e-s)+";");
	}
	
	
	private String printArray(int[] arr) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		
		for(int i : arr) {
			sb.append(i).append(",");
		}
		
		if(sb.length()>0) sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",")+1, "}");
		return sb.toString();
	}
	
	// extract real heap array depending on the heap size variable to avoid possible null elements
	private int[] getHeapArray(MaxHeap h) {
		int[] tmp = h.getHeap();
		int[] arr = new int[h.size()];

		if (h.size() >= 0) System.arraycopy(tmp, 0, arr, 0, h.size());
		return arr;
	}

    
    private Set<Object> setOf(Object[] array) {
        return Arrays.stream(array).collect(Collectors.toSet());
		//return setOf(Arrays.stream(expected).boxed().toArray( Integer[]::new ));
    }

    private boolean testMaxHeapStructure(int[] heap, int index) {
        int[] children = childrenIndices(heap, index);
        if(children.length <= 0) return true;
        if(heap[children[0]] > heap[index]) return false;
        if(children.length <= 1) return true;
        if(heap[children[1]] > heap[index]) return false;
        return testMaxHeapStructure(heap, children[0]) && testMaxHeapStructure(heap, children[1]);
    }

	private boolean testMinHeapStructure(int[] heap, int index) {
		// get children indices of node at index
		int[] children = childrenIndices(heap, index);
		if(children.length <= 0)
			return true;
		if(heap[children[0]] < heap[index])
			return false;
		if(children.length <= 1)
			return true;
		if(heap[children[1]] < heap[index])
			return false;
		return testMinHeapStructure(heap, children[0]) && testMinHeapStructure(heap, children[1]);
	}

	private int[] childrenIndices(int[] heap, int index) {
		index = index+1;
		int c1 = 2*index-1;
		int c2 = 2*index;

		// System.out.println(index + " => " + c1 + ", " + c2);
		if(c1 > heap.length-1) {
			return new int[0];
		}
		if(c2 > heap.length-1) {
			int[] a = new int[1];
			a[0] = c1;
			return a;
		}
		int[] a = new int[2];
		a[0] = c1;
		a[1] = c2;
		return a;
	}
    
    private String printHeapArray(int[] arrCurHeap) {
		 StringBuilder sb = new StringBuilder();
		 final String strIndent = "     ";
		 int maxLength = arrCurHeap.length;
		 
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
		sb.append("\n"+strIndent+"your heap\t");
		for(int i = 0; i < arrCurHeap.length;++i) {
			sb.append(String.format("%2d\t", arrCurHeap[i]));
		}
			 
		 sb.append("\n"+strIndent+"-->");
		 return sb.toString();
	}

	private String printHeapArray(int[] arrExpected, int[] arrCurHeap) {
		StringBuilder sb = new StringBuilder();
		final String strIndent = "     ";
		int maxLength = Math.max(arrExpected.length, arrCurHeap.length);

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
		sb.append("\n"+strIndent+"your heap\t");
		for(int i = 0; i < arrCurHeap.length;++i) {
			sb.append(String.format("%2d\t", arrCurHeap[i]));
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

