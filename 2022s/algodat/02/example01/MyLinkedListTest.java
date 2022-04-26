package assignment02.example01;

import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;


public class MyLinkedListTest {

	/**************************************************************************************************************
	 * Test ADT MyLinkedList
	 *************************************************************************************************************/
	public MyLinkedList list = null;
	private MyListNode TestListHead = null;
	private MyListNode TestListTail = null;
	
	private final int[] arrListDefault = {1,4,6,7,10,22,43,232};
	private final int[] arrListShort = {1,4,6,7,10};
	private final int[] arrListWithDuplicates = {2,2,3,3,3,4,8,8};
	private final int[] arrListWithoutDuplicates = {2,3,4,8};
	private final int[] arrListReorderDuplicates1 = {1,1,2,2,3,3,3,4,8,8,9,9};
	private final int[] arrListReorderDuplicates1Result = {1,1,3,3,3,9,9,2,2,4,8,8};
	private final int[] arrListReorderDuplicates2 = {2,2,4,5,5,6,8,8};
	private final int[] arrListReorderDuplicates2Result = {5,5,2,2,4,6,8,8};
	private final int[] arrListReorder1   		= {2,4,5,9};
	private final int[] arrListReorder1Result 	= {5,9,2,4};
	private final int[] arrListReorder1Element  = {1};
	private final int[] arrListReorderOnlyOddElements = {1,3,9,13,27,99};
	private final int[] arrListReorderOnlyEvenElements= {2,8,10,20,24,26};
	

	@Test
	public void testRemoveDuplicates() {
		try {
			createListFromArray(arrListWithDuplicates);
			list = new MyLinkedList(TestListHead, TestListTail, arrListWithDuplicates.length);
			String result;
			
			result = testListForward(list.getHead(), list.getTail(), arrListWithDuplicates);
			assertNull(result, result);
			result = testListBackward(list.getHead(), list.getTail(), arrListWithDuplicates);
			assertNull(result, result);

			list.removeDuplicates();

			result = testListForward(list.getHead(), list.getTail(), arrListWithoutDuplicates);
			assertNull(result, "Method 'removeDuplicates()' on list ("+arrayToString(arrListWithDuplicates)+") failed: "+result);
			result = testListBackward(list.getHead(), list.getTail(), arrListWithoutDuplicates);
			assertNull(result, "Method 'removeDuplicates()' on list ("+arrayToString(arrListWithDuplicates)+") failed: "+result);
		} catch (Exception ex) {
			fail("Method 'removeDuplicates() on list ("+arrayToString(arrListWithDuplicates)+") produced a '"+ex+"'\0");
		}
	}
	
	
	@Test
	public void testSizeWithInsertOnly() {
		try {
			list = new MyLinkedList();
					
			assertEquals(0, list.getSize(), "Empty list must have size 0!\n -->");
			
			list.insertSorted(4);
			assertEquals(1, list.getSize(), "List after inserting one element must have size 1!\n -->");
			list.insertSorted(29);
			assertEquals(2, list.getSize(), "List after inserting two elements must have size 2!\n -->");
			list.insertSorted(133);
			assertEquals(3, list.getSize(), "List after inserting three elements must have size 3!\n -->");
			list.insertSorted(81);
			assertEquals(4, list.getSize(), "List after inserting four elements must have size 4!\n -->");
		} catch(Exception ex) {
			fail("Method 'insertSorted()' produced '"+ ex +"'\0");
		}
	}
	
	@Test
	public void testSizeWithInsertAndRemove() {
		try {
			list = new MyLinkedList();
			assertEquals(0, list.getSize(), "Empty list must have size 0!\n -->");
		
			list.insertSorted(2);
			assertEquals(1, list.getSize(),"List after inserting one element must have size 1!\n -->");
			list.insertSorted(3);
			assertEquals(2, list.getSize(),"List after inserting two elements must have size 2!\n -->");
			list.insertSorted(1);
			assertEquals(3, list.getSize(),"List after inserting three elements must have size 3!\n -->");
			list.insertSorted(8);
			assertEquals(4, list.getSize(), "List after inserting four elements must have size 4!\n -->");
			
			list.remove(2);
			assertEquals(3, list.getSize(),"After removing one element of a list with 4 elements must have size 3!\n -->");
			list.remove(8);
			assertEquals(2, list.getSize(), "After removing one element of a list with 3 elements must have size 2!\n -->");
			list.remove(1);
			assertEquals(1, list.getSize(), "After removing one element of a list with 2 elements must have size 1!\n -->");
			list.remove(3);
			assertEquals(0, list.getSize(),"After removing one element of a list with 1 element must have size 0!\n -->");
		} catch(Exception ex) {
			fail(ex);
		}
	}
	
		
	@Test
	public void testInsertSorted() {
		try {
			String result;
			list = new MyLinkedList();
			
			// at beginning (empty list) head/tail must be null
			assertNull(list.getHead(),"In an empty list head must point to null!\n -->");
			assertNull(list.getTail(),"In an empty list tail must point to null!\n -->");
				
			list.insertSorted(2);
			assertNull(list.getHead().getPrev(), "After inserting one element head->prev must point to null!\n -->");
			assertNull(list.getTail().getNext(), "After inserting one element tail->next must point to null!\\n -->");
			
			list.insertSorted(5);
			result = testListForward(list.getHead(), list.getTail(), new int[]{2,5});
			assertNull(result, "After inserting e.g. [2][5]: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), new int[]{2,5});
			assertNull(result, "After inserting e.g. [2][5]: "+result+"\n -->");
			
			list.insertSorted(4);
			result = testListForward(list.getHead(), list.getTail(), new int[]{2,4,5});
			assertNull(result, "After inserting e.g. [2][5][4]: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), new int[]{2,4,5});
			assertNull(result, "After inserting e.g. [2][5][4]: "+result+"\n -->");
			
			list.insertSorted(1);
			result = testListForward(list.getHead(), list.getTail(), new int[]{1,2,4,5});
			assertNull(result, "After inserting e.g. [2][5][4][1]: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), new int[]{1,2,4,5});
			assertNull(result, "After inserting e.g. [2][5][4][1]: "+result+"\n -->");
			
			list.insertSorted(9);
			result = testListForward(list.getHead(), list.getTail(), new int[]{1,2,4,5,9});
			assertNull(result, "After inserting e.g. [2][5][4][1][9]: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), new int[]{1,2,4,5,9});
			assertNull(result, "After inserting e.g. [2][5][4][1][9]: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'insertSorted()' produced '"+ ex +"'\0");
		}
	}

	@Test
	public void testInsertSorted3EqualKeys() {
		try {
			list = new MyLinkedList();
			
			list.insertSorted(2);
			assertEquals(2, list.getHead().getElement(), "Method 'insertSorted()': After inserting one a valid element the head element is not correct!\n -->");
			assertEquals(2, list.getTail().getElement(),"Method 'insertSorted()': After inserting one a valid element the tail element is not correct!\n -->");
			assertTrue(list.getHead() == list.getTail(), "Method 'insertSorted()': After inserting one a valid element the head and tail reference must point to the same element!\n -->");
			
			list.insertSorted(2);
			assertEquals(2, list.getHead().getElement(), "Method 'insertSorted()': After inserting two equal and valid elements the head element is not correct!\n -->");
			assertEquals(2, list.getTail().getElement(),"Method 'insertSorted()': After inserting two equal and valid elements the tail element is not correct!\n -->");
			assertFalse(list.getHead()== list.getTail(), "Method 'insertSorted()': After inserting two equal and valid elements the head and tail reference must not have the same reference!\n -->");
		} catch(Exception ex) {
			fail("Method 'insertSorted()' produced '"+ ex +"'\0");
		}
	}
	
	
	@Test
	public void testReorderList() {
		try {
			createListFromArray(arrListReorder1);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorder1.length);
			String result;
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorder1);
			
			assertNull(result, "ERROR in replacing test list!!!");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorder1);
			assertNull(result, "ERROR in replacing test list!!!");
			
			int firstEvenPos = list.reorderList();
			//	assertEquals(2,firstEvenPos, "The position with the first even element is off by "+Math.abs(2-firstEvenPos)+"\0");
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorder1Result);
			assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorder1)+ "): "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorder1Result);
			assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorder1)+ "): "+result+"\n -->");
		}  catch (Exception ex) {
			fail("Method 'reorderList()' on list ("+arrayToString(arrListReorder1)+ ") produced '"+ ex +"'\0");
		}
	}
	
	@Test
	public void testReorderListWith1Element() {
		try {
			createListFromArray(arrListReorder1Element);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorder1Element.length);
			String result;
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorder1Element);
			assertNull(result, "ERROR in replacing test list!!!\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorder1Element);
			assertNull(result, "ERROR in replacing test list!!!\n -->");
			
			int firstEvenPos = list.reorderList();
			//	assertEquals(-1,firstEvenPos, "The position with the first even element is off by "+Math.abs(-1-firstEvenPos)+"\0");
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorder1Element);
			assertNull(result, "Method 'reorderList()' on list with 1 element: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorder1Element);
			assertNull(result, "Method 'reorderList()' on list with 1 element: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'reorderList()' on list with 1 element produced '"+ ex +"'\0");
		}
	}
	
	@Test
	public void testReorderListWithOnlyOddElements() {
		try {
		createListFromArray(arrListReorderOnlyOddElements);
		list = new MyLinkedList(TestListHead, TestListTail, arrListReorderOnlyOddElements.length);
		String result;
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		
		int firstEvenPos = list.reorderList();
		//	assertEquals(-1,firstEvenPos, "The position with the first even element is off by "+Math.abs(-1-firstEvenPos)+"\0");
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
		assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderOnlyOddElements)+ ") with odd elements only: "+result+"\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
		assertNull(result, "Method 'reorderList()' on list with odd elements only: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'reorderList()' on list ("+arrayToString(arrListReorderOnlyOddElements)+ ") with odd elements only produced '"+ ex +"'\0");
		}
	}
	

	@Test
	public void testReorderListWithOnlyEvenElements() {
		try {
		createListFromArray(arrListReorderOnlyEvenElements);
		list = new MyLinkedList(TestListHead, TestListTail, arrListReorderOnlyEvenElements.length);
		String result;
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		
		int firstEvenPos = list.reorderList();
		//assertEquals(0,firstEvenPos, "The position with the first even element is off by "+Math.abs(0-firstEvenPos)+"\0");
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
		assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderOnlyEvenElements)+") with even elements only: "+result+"\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
		assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderOnlyEvenElements)+") with even elements only: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'reorderList()' on list ("+arrayToString(arrListReorderOnlyEvenElements)+") with even elements only produced '"+ ex +"'\0");
		}
	}
	
	@Test
	public void testReorderListWithDuplicates() {
		try {
		createListFromArray(arrListReorderDuplicates1);
		list = new MyLinkedList(TestListHead, TestListTail, arrListReorderDuplicates1.length);
		String result;
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderDuplicates1);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderDuplicates1);
		assertNull(result, "ERROR in replacing test list!!!\n -->");
		
		int firstEvenPos = list.reorderList();
		//assertEquals(7,firstEvenPos, "The position with the first even element is off by "+Math.abs(7-firstEvenPos)+"\0");
		
		result = testListForward(list.getHead(), list.getTail(), arrListReorderDuplicates1Result);
		assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates1)+") with duplicates failed: "+result+"\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListReorderDuplicates1Result);
		assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates1)+") with duplicates failed: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates1)+") with duplicates produced '"+ ex +"'\0");
		}
	}
	
	@Test
	public void testReorderListWithDuplicates2() {
		try {
			createListFromArray(arrListReorderDuplicates2);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorderDuplicates2.length);
			String result;
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorderDuplicates2);
			assertNull(result, "ERROR in replacing test list!!!\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorderDuplicates2);
			assertNull(result, "ERROR in replacing test list!!!\n -->");
			
			int firstEvenPos = list.reorderList();
			//assertEquals(2,firstEvenPos, "The position with the first even element is off by "+Math.abs(2-firstEvenPos)+"\0");
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorderDuplicates2Result);
			assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates2)+ ") with duplicates failed: "+result+"\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorderDuplicates2Result);
			assertNull(result, "Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates2)+ ") with duplicates failed: "+result+"\n -->");
		} catch(Exception ex) {
			fail("Method 'reorderList()' on list ("+arrayToString(arrListReorderDuplicates2)+ ") with duplicates produced '"+ex+"'\0");
		}
	}
	
	
	// test the return value of the reorderList-method separately
	@Test
	public void testReorderReturnValue() {
		try {
			createListFromArray(arrListReorderDuplicates2);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorderDuplicates2.length);
			String result;
			
			result = testListForward(list.getHead(), list.getTail(), arrListReorderDuplicates2);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorderDuplicates2);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			
			int firstEvenPos = list.reorderList();
						
			assertEquals(2,firstEvenPos,"Method 'reorderList() return wrong value. The position with the first even element is off by "+Math.abs(2-firstEvenPos)+"\0");
			
			
			// 2nd test with odd elements only
			createListFromArray(arrListReorderOnlyOddElements);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorderOnlyOddElements.length);

			result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyOddElements);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			
			firstEvenPos = list.reorderList();
			
			assertEquals(-1,firstEvenPos,"Method 'reorderList() return wrong value of list with odd elements only. The position with the first even element is off by "+Math.abs(-1-firstEvenPos)+"\0");
			
			// 3rd test with even elements only
			createListFromArray(arrListReorderOnlyEvenElements);
			list = new MyLinkedList(TestListHead, TestListTail, arrListReorderOnlyEvenElements.length);

			result = testListForward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			result = testListBackward(list.getHead(), list.getTail(), arrListReorderOnlyEvenElements);
			assertNull(result,"ERROR in replacing test list!!!\n -->");
			
			firstEvenPos = list.reorderList();
			
			assertEquals(0,firstEvenPos,"Method 'reorderList() returns wrong value of list with even elements only. The position with the first even element is off by "+Math.abs(-firstEvenPos)+"\0");
		} catch(Exception ex) {
			fail("Method 'reorderList()' produced '"+ex+"' when testing for correct return value.\0");
		}
	}

	
	@Test
	public void testClear() {
		try {
			createListFromArray(arrListDefault); //{1,4,6,7,10,22,43,232};
			list = new MyLinkedList(TestListHead, TestListTail, arrListDefault.length);

			list.clear();
			assertEquals(0, list.getSize(),"Method 'clear()': After clearing the list getSize() should return 0!\n -->");
			assertNull(list.getHead(),"Method 'clear()': After clearing the list head should point to null!\n -->");
			assertNull(list.getTail(),"Method 'clear()': After clearing the list tail should point to null!\n -->");
		} catch(Exception ex) {
			fail(ex);
		}
	}

			
	@Test
	public void testGet() {
		
		String reason = "Method 'get()': Wrong element returned!\n -->";
		createListFromArray(arrListDefault);	//{1,4,6,7,10,22,43,232};
		list = new MyLinkedList(TestListHead, TestListTail, arrListDefault.length);
		
		assertEquals(1, list.get(0),reason);
		assertEquals(4, list.get(1),reason);
		assertEquals(6, list.get(2),reason);
		assertEquals(7, list.get(3),reason);
		assertEquals(10, list.get(4),reason);
		assertEquals(22, list.get(5),reason);
		assertEquals(43, list.get(6),reason);
		assertEquals(232, list.get(7),reason);
		
		try { 
			list.get(21); 
		} catch(Exception e) {
			assertTrue(e instanceof IllegalArgumentException,"Method 'get': Accessing a position out of bounds should throw an IllegalArgumentException!\n -->");
		}
		try { 
			list.get(-1); 
		} catch(Exception e) {
			assertTrue(e instanceof IllegalArgumentException,"Method 'get': Accessing a position out of bounds (e.g. -1) should throw an IllegalArgumentException!\n -->");
		}
	}

	@Test
	public void testRemoveOnEmptyList() {
		try {
		list = new MyLinkedList();
		assertFalse(list.remove(0),"Method 'remove()': Removing an element from an empty list should return false!\n -->");
		} catch(Exception ex) {
			fail("Method 'remove()': Removing an element from an empty list should return false but produced an '"+ex+"'\0");
		}
	}
	
	@Test
	public void testRemove() {	
		try {
		String result;
		String reason = "Method 'remove()': Element couldn't be removed correctly!\n --> ";
		createListFromArray(arrListShort);	//{1,4,6,7,10};
		list = new MyLinkedList(TestListHead, TestListTail, arrListShort.length);
		
		result = testListForward(list.getHead(), list.getTail(), arrListShort);
		assertNull(result,"ERROR in replacing test list!!!\n -->");
		result = testListBackward(list.getHead(), list.getTail(), arrListShort);
		assertNull(result,"ERROR in replacing test list!!!\n -->");
		
		assertTrue(list.remove(1),reason+"Return value of remove() is wrong when removing the first element of the list.\0");
		result = testListForward(list.getHead(), list.getTail(), new int[]{4,6,7,10});
		assertNull(result,reason+"Somewhere a 'next' link is wrong when removing the first element of the list.\0");
		result = testListBackward(list.getHead(), list.getTail(), new int[]{4,6,7,10});
		assertNull(result,reason+"Somewhere a 'prev' link is wrong when removing the first element of the list.\0");
		
		
		assertTrue(list.remove(10),reason+"Wrong return value when trying to remove not existing element.\0");
		result = testListForward(list.getHead(), list.getTail(), new int[]{4,6,7});
		assertNull(result,reason+"Somewhere a 'next' link is wrong when removing a not existing element.\0");
		result = testListBackward(list.getHead(), list.getTail(), new int[]{4,6,7});
		assertNull(result,reason+"Somewhere a 'prev' link is wrong when removing a not existing element.\0");
		
		assertTrue( list.remove(6),reason+"Wrong return value when removing an existing element (not head and not tail).\0");
		result = testListForward(list.getHead(), list.getTail(), new int[]{4,7});
		assertNull(result,reason+"Somewhere a 'next' link is wrong when remoting an existing element (not head and not tail).\0");
		result = testListBackward(list.getHead(), list.getTail(), new int[]{4,7});
		assertNull(result,reason+"Somewhere a 'prev' link is wrong when remoting an existing element (not head and not tail).\0");
		
		assertTrue(list.remove(4),reason+"Return value of remove() is wrong when removing the first element of a 2 element list.\0");
		result = testListForward(list.getHead(), list.getTail(), new int[]{7});
		assertNull(result,reason+"Somewhere a 'next' link is wrong when removing the first element of a 2 element list.\0");
		result = testListBackward(list.getHead(), list.getTail(), new int[]{7});
		assertNull(result,reason+"Somewhere a 'prev' link is wrong when removing the first element of a 2 element list.\0");
		
		
		assertFalse(list.remove(-1),"Method 'remove()': Removing an element which is not in the list should return false!\n -->");
		
		
		assertTrue(list.remove(7),reason+"Wrong return value when removing the last existing element of a list.\0");
		assertNull(list.getHead(),"Method 'remove()': After removing all elements from list head reference should be null!\n -->");
		assertNull(list.getTail(),"Method 'remove()': After removing all elements from list tail reference should be null!\n -->");
		assertEquals(0, list.getSize(),"Method 'remove()': After removing all elements from list the list size should be 0!\n -->");
		} catch(Exception ex) {
			fail(ex);
		}
	}
	
	@Test
	public void testGetFromEmptyList() {
		list = new MyLinkedList();
		assertNull(list.getHead(),"Method 'get()': In a new MyLinkedList() the head reference should be null!\n -->");
		assertNull(list.getTail(),"Method 'get()': In a new MyLinkedList() the tail reference should be null!\n -->");
		assertEquals(0, list.getSize(),"Method 'get()': In a new MyLinkedList() the size should be 0!\n -->");

		
		try { 
			list.get(0); 
		} catch(Exception e) {
			assertTrue(e instanceof IllegalArgumentException,"Method 'get()': The attempt of getting any element from an empty list should throw an IllegalArgumentException!\n -->");
		}
	}
	


	/**********************************
	* private help methods
	***********************************/
	
	private boolean createListFromArray(int[] arrList) {
		// reset head and tail
		TestListHead = null;
		TestListTail = null;

		if (arrList.length > 0) {
			// store first element and update head and tail
			TestListHead = new MyListNode(arrList[0]);
			TestListTail = TestListHead;

			for (int i = 1; i < arrList.length; i++) {

				MyListNode n = new MyListNode(arrList[i]);
				n.setPrev(TestListTail);
				TestListTail.setNext(n);
				TestListTail = n;
			}
			return true;
		} else {
			return false;
		}
	}

	// This method verifies a list (head to tail) forward by comparing it against a predefined
	// list (array). If it's correct, null is returned, otherwise an error message is returned.
	private String testListForward(MyListNode head, MyListNode tail, int[] list) {
		MyListNode current = head;

		if (list.length == 0){
			if(head == null && tail == null) return null;
			else return "List should be empty - head or tail is not null!\0";
		}
		else if(list.length == 1) {
			if (head != tail) return "Head and tail are not equal in a list with size 1!\0";
			if (head.getNext() != null) return "Next of Head/Tail should be null (listsize == 1)!\0";
			if (head.getPrev() != null) return "Prev of Head/Tail should be null (listsize == 1)!\0";
			if (list[0] != head.getElement())
				return "Wrong element at index 0 (head)! Expected ["+ list[0] +"] but found ["+ head.getElement() +"]\0";
			else return null;
		}

		// list with size > 1
		for (int i = 0; i < list.length; i++) {
			if(current == head) {
				if(current.getNext() == null) return "Next of head is null (listsize > 1)!\0";
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+" (head)! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";
				if(list[i+1] != current.getNext().getElement())
					return "Wrong next element of index "+i+" (head)! Expected ["+ list[i + 1] +"] but found ["+ current.getNext().getElement() +"]\0";

			} else if(current == tail) {
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+" (tail)! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";
				if(current.getNext() != null) return "Next of tail is not null!\0";

			}else {
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+"! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";

				if (current.getNext() == null) {
					return "Wrong next element of index "+i+"! Expected ["+ list[i + 1] +"] but found null!\0";
				} else {
					if (list[i+1] != current.getNext().getElement())
						return "Wrong next element of index "+i+"! Expected ["+ list[i + 1] +"] but found ["+ current.getNext().getElement() +"]\0";
				}

			}
			current = current.getNext();
		}
		return null;
	}

	private String testListBackward(MyListNode head, MyListNode tail, int[] list) {
		MyListNode current = tail;

		if (list.length == 0){
			if(head == null && tail == null) return null;
			else return "List should be empty - head or tail is not null!\0";
		}
		else if(list.length == 1) {
			if (head != tail) return "Head and tail are not equal in a list with size 1!\0";
			if (tail.getPrev() != null) return "Prev of Head/Tail should be null (listsize == 1)!\0";
			if (tail.getNext() != null) return "Next of Head/Tail should be null (listsize == 1)!\0";
			if (list[list.length-1] != tail.getElement())
				return "Wrong element at index 0 (head)! Expected ["+ list[list.length - 1] +"] but found ["+ tail.getElement() +"]\0";
		}

		// list with size > 1
		for (int i = list.length-1; i >= 0; i--) {
			if(current == head) {
				if(current.getPrev() != null) return "Prev of head is not null (listsize > 1)!\0";
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+" (head)! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";

			} else if(current == tail) {
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+" (tail)! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";
				if(current.getPrev() == null) return "Prev of tail is null!\0";

			}else {
				if(list[i] != current.getElement())
					return "Wrong element at index "+i+"! Expected ["+ list[i] +"] but found ["+ current.getElement() +"]\0";

				//assert(current.getPrev()==null,"Wrong prev element of index "+i+"! Expected ["+list[i+1].intValue()+"] but found null!");
				if(current.getPrev() == null) {
					return "Wrong prev element of index "+i+"! Expected ["+ list[i + 1] +"] but found null!\0";
				} else {
					if (list[i-1] != current.getPrev().getElement())
						return "Wrong prev element of index "+i+"! Expected ["+ list[i - 1] +"] but found ["+ current.getPrev().getElement() +"]"+'\0';
				}
			}
			current = current.getPrev();
		}
		return null;
	}

	private String arrayToString(int[] arr) {
		StringBuilder sb = new StringBuilder();
		for (int c : arr) {
			sb.append("[").append(c).append("]");
		}
	
		return sb.toString();
	}
	
}
// EOT11
