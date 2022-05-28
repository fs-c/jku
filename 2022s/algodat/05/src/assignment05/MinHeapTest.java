package assignment05;

import assignment05.MinHeap;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.Arrays;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

public class MinHeapTest {
		
	/**************************************************************************************************************
	 * ************************************
	 * Test PQ/HEAP
	 * 
	 * ************************************
	 *************************************************************************************************************/
	
	private final int[] heap012 = {0,1,2};
	private final int[] heap201 = {2,0,1};
	private final int[] heap201removeMinResult = {1,2};
    private final int[] heap102 = {1,0,2};
    private final int[] heap102result = {0,1,2};
    private final int[] heap43210 = {4,3,2,1,0};
    private final int[] heap43210result = {0,1,3,4,2};
    private final int[] heap43210removeMinResult = {1,2,3,4};

    private final int[] heap0 = {0};

	private void testMinHeapProperties(String strHeader, int[] expected, MinHeap heap) {
        Set<Object> expectedSet = setOf(Arrays.stream(expected).boxed().toArray( Integer[]::new ));
		int[] actual = Arrays.copyOfRange(heap.getHeap(),0,heap.size());
		Set<Object> actualSet = setOf(Arrays.stream(actual).boxed().toArray( Integer[]::new ));

		assertEquals(expected.length, actual.length, strHeader+" failed because of wrong lengths: \n"+printHeapArray(expected, actual));
        assertEquals(expectedSet, actualSet, strHeader+" failed because heap properties are not met!\n"+printHeapArray(expected, actual));
        assertTrue(testMinHeapStructure(actual, 0), strHeader+" failed because heap order property is not met!\n"+printHeapArray(expected, actual));
    }
    
    private Set<Object> setOf(Object[] array) {
        return Arrays.stream(array).collect(Collectors.toSet());
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
    
    private void insertIntoHeap(MinHeap heap, int[] arr) {
    	for (int i = 0; i < arr.length; ++i) {
    		heap.insert(arr[i]);
    	}
    }
    
    @Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertWithOneElement() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
    	try {
    		heap = new MinHeap(heap0.length);
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because heap could not be created: ");
    	
    	try {
    		insertIntoHeap(heap,heap0);
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed as no elements could be inserted into heap: " + exCaught);
    	
    	try {
    		testMinHeapProperties("heapPQ.insert() and input sequence "+printInputSequence(heap0),heap0, heap);
    	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because heap with input sequence " + printInputSequence(heap0) + " couldn't be analyzed because of: " + exCaught);
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertWithUpHeapOfMiddleElement() {
       	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap102.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap102);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed as no elements could be inserted into heap: " + exCaught);
       	
       	try {
       		testMinHeapProperties("heapPQ.insert() and input sequence "+printInputSequence(heap102),heap102result, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because your heap with input sequence " + printInputSequence(heap102) + " couldn't be analyzed because of: " + exCaught);
    }
    
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertWithUpHeapOfLastElement() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
		try {
			heap = new MinHeap(3);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as no assignment4.MinHeap could be created: " + exCaught);
		
		try {
			heap.insert(2);
			heap.insert(3);
			heap.insert(1);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as inserting elements with insert() caused: " + exCaught);
		
		try {
			final String strErr = "heapPQ.insert() failed for input sequence [2,3,1] ";
			
			assertEquals(1,heap.getHeap()[0], strErr+"because of wrong element at index position 0: ");
			assertEquals(3,heap.getHeap()[1], strErr+"because of wrong element at index position 1: ");
			assertEquals(2,heap.getHeap()[2], strErr+"because of wrong element at index position 2: ");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as .getHeap() caused: " + exCaught);
    }

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapInsertWithUpHeapOfLastElementIncludingNegatives() {
		Exception exCaught = null;
		MinHeap heap = null;

		try {
			heap = new MinHeap(3);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as no assignment4.MinHeap could be created: " + exCaught);

		try {
			heap.insert(2);
			heap.insert(3);
			heap.insert(-1);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as inserting elements with insert() caused: " + exCaught);

		try {
			final String strErr = "heapPQ.insert() failed for input sequence [2,3,-1] ";

			assertEquals(-1,heap.getHeap()[0], strErr+"because of wrong element at index position 0: ");
			assertEquals(3,heap.getHeap()[1], strErr+"because of wrong element at index position 1: ");
			assertEquals(2,heap.getHeap()[2], strErr+"because of wrong element at index position 2: ");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as .getHeap() caused: " + exCaught);
	}

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapInsertWithUpHeapOfLastElementIncludingEqualKeys() {
		Exception exCaught = null;
		MinHeap heap = null;

		try {
			heap = new MinHeap(3);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as no assignment4.MinHeap could be created: " + exCaught);

		try {
			heap.insert(2);
			heap.insert(3);
			heap.insert(2);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as inserting elements with insert() caused: " + exCaught);

		try {
			final String strErr = "heapPQ.insert() failed for input sequence [2,3,2] ";

			assertEquals(2,heap.getHeap()[0], strErr+"because of wrong element at index position 0: ");
			assertEquals(3,heap.getHeap()[1], strErr+"because of wrong element at index position 1: ");
			assertEquals(2,heap.getHeap()[2], strErr+"because of wrong element at index position 2: ");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.insert() could not be tested as .getHeap() caused: " + exCaught);
	}
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertWithoutUpHeap() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap012.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap012);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed as no elements could be inserted into heap: " + exCaught);

       	try {
       		testMinHeapProperties("heapPQ.insert() and input sequence "+printInputSequence(heap012),heap012, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because your heap couldn't be analyzed because of: " + exCaught);
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertWithMultipleUpHeap() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap43210.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap43210);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed as no elements could be inserted into heap: " + exCaught);
       	try {
       		testMinHeapProperties("heapPQ.insert() and input sequence "+printInputSequence(heap43210),heap43210result, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because your heap couldn't be analyzed because of: " + exCaught);
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapInsertInCapacity1WithDoublingCapacity() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(1);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed because heap with size 1 could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap43210);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.insert() failed as no elements could be inserted into heap: " + exCaught);
       	try {
       		testMinHeapProperties("heapPQ.insert() in heap with initial capacity 1 and input sequence "+printInputSequence(heap43210),heap43210result, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.insert() failed because your heap couldn't be analyzed because of: " + exCaught);
    }
    

    @Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapIsEmpty() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
    	try {
    		heap = new MinHeap(10);
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.isEmpty() failed because heap could not be created: ");
    	
    	try {
    		assertTrue(heap.isEmpty(), "heapPQ.isEmpty() is false for empty heap.");
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.isEmpty() failed because function call caused: " + exCaught);
    	try {
    		heap.insert(10);
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.isEmpty() failed because call of insert() caused: " + exCaught);
    	
    	try {
    		assertFalse(heap.isEmpty(), "heapPQ.isEmpty() is true for heap with 1 element.");
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.isEmpty() could not be tested because .isEmpty() caused " + exCaught);
    }

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapIsEmptyUsingRemove() {
		Exception exCaught = null;
		MinHeap heap = null;

		try {
			heap = new MinHeap(10);
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() failed because heap could not be created: ");

		try {
			assertTrue(heap.isEmpty(), "heapPQ.isEmpty() is false for empty heap.");
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() failed because function call caused: " + exCaught);

		try {
			heap.insert(10);
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() failed because call of insert() caused: " + exCaught);

		try {
			assertFalse(heap.isEmpty(), "heapPQ.isEmpty() is true for heap with 1 element.");
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() could not be tested because .isEmpty() caused " + exCaught);

		try {
			heap.removeMin();
		} catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() failed because call of removeMin() caused: " + exCaught);

		try {
			assertTrue(heap.isEmpty(), "heapPQ.isEmpty() is false for empty heap (after removeMin()).");
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.isEmpty() could not be tested because .isEmpty() caused " + exCaught);
	}
    
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapMin() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
    	try {
    		heap = new MinHeap(1);
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because heap could not be created: ");
    	
    	try {
    		heap.insert(10);
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed as no elements could be inserted into heap: " + exCaught);
    	
    	// verify that we have a valid heap
    	try {
    		testMinHeapProperties("heapPQ.min() and input sequence "+printInputSequence(new int[] {10}),new int[]{10}, heap);
    	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because your heap couldn't be analyzed because of: " + exCaught);
    
    	// call min()
    	try {
    		assertEquals(10, heap.min(), "heapPQ.min() on heap with input sequence [10] returned wrong result: ");
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because .min() caused: " + exCaught);

		// heap still must not be empty, as min() does no removal
		try {
			assertEquals(1, heap.size(), "heapPQ.size() on heap with input sequence [10] returned wrong result: ");
		}catch(Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.min() failed because .size() caused: " + exCaught);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapMinWithMultipleElements() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
    	try {
    		heap = new MinHeap(1);
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because heap could not be created: ");
    	
    	try {
    		insertIntoHeap(heap, heap43210);
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed as no elements could be inserted into heap: " + exCaught);
    	
    	// verify that we have a valid heap
    	try {
    		testMinHeapProperties("heapPQ.min() and input sequence "+printInputSequence(heap43210),heap43210result, heap);
    	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because your heap couldn't be analyzed because of: " + exCaught);
    
    	// call min()
    	try {
    		assertEquals(0, heap.min(), "heapPQ.min() on heap with input sequence "+printInputSequence(heap43210)+" returned wrong result: ");
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because min() caused: " + exCaught);
    }
    
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapMinOnEmptyHeap() {
    	Exception exCaught = null;
    	MinHeap heap = null;
    	
    	try {
    		heap = new MinHeap(1);
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.min() failed because heap could not be created: ");
    	
    	try {
    		heap.min();
    	}catch(Exception ex) {
    		exCaught = ex;
    	}
    	
    	assertTrue(exCaught instanceof NoSuchElementException, "heapPQ.min() on empty heap should throw a NoSuchElementException. Your implementation caused: "+exCaught);
    }
    
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapRemoveMinLastElement() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap0.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap0);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed as no elements could be inserted into heap: " + exCaught);
        
        // check removeMin() return value
       	try {
       		assertEquals(0,heap.removeMin(), "heapPQ.removeMin() returned wrong result on heap with input sequence "+printInputSequence(heap0)+": ");
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() on heap with one element only failed because of: " + exCaught);
       	
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapRemoveMinWithoutDownheap() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap201.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap201);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed as no elements could be inserted into heap: " + exCaught);
       
       	try {
       		testMinHeapProperties("heapPQ.removeMin() and input sequence "+printInputSequence(heap201),heap201, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed because your heap couldn't be analyzed because of: " + exCaught);
    	
    	// check removeMin() return value
    	try {
    		assertEquals(0,heap.removeMin(), "heapPQ.removeMin() returned wrong result on heap with input sequence "+printInputSequence(heap201)+": ");
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed when calling removeMin() on heap with input sequence " + printInputSequence(heap201) + " because of: " + exCaught);
    	
    	// check remaining heap
    	try {
       		testMinHeapProperties("heapPQ.removeMin() on heap with input sequence "+printInputSequence(heap201)+" + calling removeMin() ",heap201removeMinResult, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed as your heap couldn't be analyzed because of: " + exCaught);
    }
    
    @Test
   	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapRemoveMinWithDownheap() {
    	Exception exCaught = null;
       	MinHeap heap = null;
       	
       	try {
       		heap = new MinHeap(heap43210.length);
       	}catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed because heap could not be created: ");
       	
       	try {
       		insertIntoHeap(heap,heap43210);
       	} catch(Exception ex) {
       		exCaught = ex;
       	}
		assertNull(exCaught, "heapPQ.removeMin() failed as no elements could be inserted into heap: " + exCaught);
       
       	try {
       		testMinHeapProperties("heapPQ.removeMin() and input sequence "+printInputSequence(heap43210),heap43210result, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed because your heap with input sequence " + printInputSequence(heap43210) + " couldn't be analyzed because of: " + exCaught);
    	
    	// check removeMin() return value
    	try {
    		assertEquals(0,heap.removeMin(), "heapPQ.removeMin() returned wrong result on heap with input sequence "+printInputSequence(heap43210removeMinResult)+": ");
    	} catch(Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed when calling removeMin() on heap with input sequence " + printInputSequence(heap43210) + " caused: " + exCaught);
    	
    	// check remaining heap
    	try {
       		testMinHeapProperties("heapPQ.removeMin() on heap with input sequence "+printInputSequence(heap43210)+" + calling removeMin() ",heap43210removeMinResult, heap);
       	} catch (Exception ex) {
    		exCaught = ex;
    	}
		assertNull(exCaught, "heapPQ.removeMin() failed as your heap with input sequence " + printInputSequence(heap43210) + " and after 1x removeMin() couldn't be analyzed because of: " + exCaught);
    }
    
    
    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeapSizeWithInsertAndRemove() {
    	Exception exCaught = null;
    	MinHeap heap = null;
		try {
			heap = new MinHeap(4);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.size() could not be tested as no assignment4.MinHeap could be created: " + exCaught);
		
		try {
			assertEquals(0, heap.size(), "heapPQ.size() for empty heap failed: ");
			heap.insert(2);
			assertEquals(1, heap.size(), "heapPQ.size() on heap with insert sequence [2] failed: ");
			heap.insert(3);
			assertEquals(2, heap.size(), "heapPQ.size() on heap with insert sequence [2,3] failed: ");
			heap.insert(1);
			assertEquals(3, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1] failed: ");
			heap.insert(8);
			assertEquals(4, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1,8] failed: ");

		}catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.size() using insert() method could not be tested because of: " + exCaught);
		
		try {
			heap.removeMin();
			assertEquals(3, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1,8] failed after calling removeMin() 1x: ");
			heap.removeMin();
			assertEquals(2, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1,8] failed after calling removeMin() 2x: ");
			heap.removeMin();
			assertEquals(1, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1,8] failed after calling removeMin() 3x: ");
			heap.removeMin();
			assertEquals(0, heap.size(), "heapPQ.size() on heap with insert sequence [2,3,1,8] failed after calling removeMin() 4x: ");
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "heapPQ.size() on heap with insert sequence [2,3,1,8] caused somewhere after calling removeMin() + size(): " + exCaught);
		
    }
    

    @Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testHeapRunTime() {
		Exception exCaught = null;
		MinHeap heap = null;
		try {
			heap = new MinHeap(1);
		} catch (Exception ex) {
			exCaught = ex;
		}
		assertNull(exCaught, "PQ-Heap runtimeTest could not be executed as no assignment4.MinHeap could be created: " + exCaught);
		
		int runs = 1000;
		long s = System.currentTimeMillis();
		for(int i = 0; i<runs; i++) {
			heap.insert(Double.valueOf(Math.random()*1000000).intValue());
		}
		long e = System.currentTimeMillis();
		System.out.println("Runs: "+runs+"; Time: "+(e-s)+";");
		
		heap = new MinHeap(1);

		runs = 50000;
		s = System.currentTimeMillis();
		for(int i = 0; i<runs; i++) {
			heap.insert(Double.valueOf(Math.random()*1000000).intValue());
		}
		e = System.currentTimeMillis();
		System.out.println("Runs: "+runs+"; Time: "+(e-s)+";");
		
		heap = new MinHeap(1);
		
		runs = 250000;
		s = System.currentTimeMillis();
		for(int i = 0; i<runs; i++) {
			heap.insert(Double.valueOf(Math.random()*1000000).intValue());
		}
		e = System.currentTimeMillis();
		System.out.println("Runs: "+runs+"; Time: "+(e-s)+";");
	}


	/**
	 * PRIVATE METHODS
	 */
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
	
	private String printInputSequence(int[] arrInputSequence) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("[");
		for(int i = 0; i < arrInputSequence.length;++i) {
			sb.append(arrInputSequence[i]).append(",");
		}
		sb.replace(sb.length()-1, sb.length(), "]");
		return sb.toString();
	}
}
// EOT11
