package assignment04;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.io.*;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;


public class MyBinarySearchTreeTest {
		
	/**************************************************************************************************************
	 * ************************************
	 * Test BST
	 * 
	 * ************************************
	 *************************************************************************************************************/

	// Test sequence: 5, 18, 1, 8, 14, 16, 13, 3
	// Resulting tree after successively inserting of the elements:
	//
	//				5
	//		1				18
	//			3		8	
	//						14
	//					13		16
	//
	//Inorder:	1, 3, 5, 8, 13, 14, 16, 18
	//Preorder:	5, 1, 3, 18, 8, 14, 13, 16
	//Postorder:3, 1, 13, 16, 14, 8, 18, 5
	
	MyBinarySearchTree tree;

	private final int[] arrList1 = {5, 18, 1, 8, 14, 16, 13, 3};
	private final int[] arrList2 = {10, 5,12,3};
	private final Integer[] arrList1inorder = {1, 3, 5, 8, 13, 14, 16, 18};
	private final Integer[] arrList1preorder = {5, 1, 3, 18, 8, 14, 13, 16};
	private final Integer[] arrList1postorder = {3, 1, 13, 16, 14, 8, 18, 5};
	//private final int[] arrListWithDuplicates = {5, 18, 1, 8, 14, 16, 13, 3, 8};
	private final File inputFilePath = new File((this.getClass().getPackageName()).replace(".", "/"));

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testInsert() {
		tree = new MyBinarySearchTree();
		
		Exception caughtException = null;
		try {
			tree.insert(5, "5"); 	
			tree.insert(18, "18"); 	
			tree.insert(1, "1");
			tree.insert(8, "8"); 	
			tree.insert(14, "14"); 	
			tree.insert(16, "16"); 	
			tree.insert(13, "13"); 	
			tree.insert(3, "3");
			final String errorMsg = "Insert() failed for sequence: "+printInputSequence(arrList1)+
					" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n";
	
			// check root
			assertEquals(5, tree.getRoot().key, errorMsg);
			
			// left subtree
			assertEquals(1, tree.getRoot().left.key, errorMsg);
			assertNull(tree.getRoot().left.left, errorMsg+"    --> Left of '1' should be null:");
			assertEquals(3, tree.getRoot().left.right.key, errorMsg);
			assertNull(tree.getRoot().left.right.left, errorMsg+"    --> Left of '3' should be null:");
			assertNull(tree.getRoot().left.right.right, errorMsg+"    --> Right of '3' should be null:");
			
			// right subtree
			assertEquals(18, tree.getRoot().right.key, errorMsg);
			assertNull(tree.getRoot().right.right, errorMsg+"    --> Right of '18' should be null:");
			
			assertEquals(8, tree.getRoot().right.left.key, errorMsg);
			assertNull(tree.getRoot().right.left.left, errorMsg+"    --> Left of '8' should be null:");
			
			assertEquals(14, tree.getRoot().right.left.right.key, errorMsg);
			assertEquals(16, tree.getRoot().right.left.right.right.key, errorMsg);
			assertEquals(13, tree.getRoot().right.left.right.left.key, errorMsg);
			
			assertNull(tree.getRoot().right.left.right.right.left, errorMsg+"    --> Left of '13' should be null:");
			assertNull(tree.getRoot().right.left.right.right.right, errorMsg+"    --> Right of '13' should be null:");
			assertNull(tree.getRoot().right.left.right.left.left, errorMsg+"    --> Left of '16' should be null:");
			assertNull(tree.getRoot().right.left.right.left.right, errorMsg+"    --> Right of '16' should be null:");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "insert() of sequence " + printInputSequence(arrList1) + " caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	// same as insert, but with duplicate at the end
	public void testInsertDuplicates() {
		tree = new MyBinarySearchTree();
		Exception caughtException = null;
		
		try {
			tree.insert(5, "5"); 	
			tree.insert(18, "18"); 	
			tree.insert(1, "1"); 	
			tree.insert(8, "8"); 	
			tree.insert(14, "14"); 	
			tree.insert(16, "16"); 	
			tree.insert(13, "13"); 	
			tree.insert(3, "3"); 	
	
			tree.insert(1, "1"); 	
			
			final String errorMsg = "Insert() with duplicates failed (should not be possible!) for sequence: "+printInputSequence(arrList1)+
					" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n";
	
			// check root
			assertEquals(5, tree.getRoot().key, errorMsg);
			
			// left subtree
			assertEquals(1, tree.getRoot().left.key, errorMsg);
			assertNull(tree.getRoot().left.left, errorMsg+"    --> Left of '1' should be null:");
			assertEquals(3, tree.getRoot().left.right.key, errorMsg);
			assertNull(tree.getRoot().left.right.left, errorMsg+"    --> Left of '3' should be null:");
			assertNull(tree.getRoot().left.right.right, errorMsg+"    --> Right of '3' should be null:");
			
			// right subtree
			assertEquals(18, tree.getRoot().right.key, errorMsg);
			assertNull(tree.getRoot().right.right, errorMsg+"    --> Right of '18' should be null:");
			
			assertEquals(8, tree.getRoot().right.left.key, errorMsg);
			assertNull(tree.getRoot().right.left.left, errorMsg+"    --> Left of '8' should be null:");
			
			assertEquals(14, tree.getRoot().right.left.right.key, errorMsg);
			assertEquals(16, tree.getRoot().right.left.right.right.key, errorMsg);
			assertEquals(13, tree.getRoot().right.left.right.left.key, errorMsg);
			
			assertNull(tree.getRoot().right.left.right.right.left, errorMsg+"    --> Left of '13' should be null:");
			assertNull(tree.getRoot().right.left.right.right.right, errorMsg+"    --> Right of '13' should be null:");
			assertNull(tree.getRoot().right.left.right.left.left, errorMsg+"    --> Left of '16' should be null:");
			assertNull(tree.getRoot().right.left.right.left.right, errorMsg+"    --> Right of '16' should be null:");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "insert() of sequence " + printInputSequence(arrList1) + ",1 caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testSizeWithInsert() {
		tree = new MyBinarySearchTree();
		final String errorMsg = "size() failed for sequence: "+printInputSequence(arrList1);
		Exception caughtException = null;
		
		try {
			assertEquals(0, tree.size(), errorMsg+"    --> Wrong size for empty tree: ");
			tree.insert(5, "5");
			assertEquals(1, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 1 element: ");
			tree.insert(18, "18");
			assertEquals(2, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 2 elements: ");
			tree.insert(1, "1"); 	
			assertEquals(3, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 3 elements: ");
			tree.insert(8, "8"); 	
			assertEquals(4, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 4 elements: ");
			tree.insert(14, "14"); 	
			assertEquals(5, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 5 elements: ");
			tree.insert(16, "16"); 	
			assertEquals(6, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 6 elements: ");
			tree.insert(13, "13"); 	
			assertEquals(7, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 7 elements: ");
			tree.insert(3, "3"); 	
			assertEquals(8, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree after inserting 8 elements: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, errorMsg + "    --> caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testSizeWithInsertDuplicates() {
		tree = new MyBinarySearchTree();
		final String errorMsg = "size() failed for sequence: "+printInputSequence(arrList1);
		Exception caughtException = null;
		
		try {
			tree.insert(5, "5");
			tree.insert(18, "18");
			tree.insert(1, "1"); 	
			tree.insert(8, "8"); 	
			tree.insert(14, "14"); 	
			tree.insert(16, "16"); 	
			tree.insert(13, "13"); 	
			tree.insert(3, "3"); 	
				
			tree.insert(1, "1"); 	
			assertEquals(8, tree.size(), errorMsg+" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n"+
					"    --> Wrong size for tree with 8 elements after inserting '1' again: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, errorMsg + ",1 --> caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testInsertInvalid() {
		tree = new MyBinarySearchTree();
		Exception expectedEx = null;
		
		try {
			tree.insert(-1, null);
		} catch (Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "Insert() with '-1' argument for key and and null as elem didn't throw an IllegalArgumentException!");
		
		try {
			tree.insert(0, null);
		} catch (Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "Insert() with 'null' argument for elem didn't throw an IllegalArgumentException!");
	}
	

	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testGetDepth() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		
		final String errorMsg = "getDepth() is wrong for sequence: "+printInputSequence(arrList1)+
				" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n";
		Exception caughtException = null;
		
		try {
			assertEquals(0,tree.getDepth(5), errorMsg+"    --> Root should have height 0: ");
			assertEquals(1,tree.getDepth(18), errorMsg+"    --> Wrong depth of node 18: ");
			assertEquals(1,tree.getDepth(1), errorMsg+"    --> Wrong depth of node 1: ");
			assertEquals(2,tree.getDepth(8), errorMsg+"    --> Wrong depth of node 8: ");
			assertEquals(2,tree.getDepth(3), errorMsg+"    --> Wrong depth of node 3: ");
			assertEquals(3,tree.getDepth(14), errorMsg+"    --> Wrong depth of node 14: ");
			assertEquals(4,tree.getDepth(13), errorMsg+"    --> Wrong depth of node 13: ");
			assertEquals(4,tree.getDepth(16), errorMsg+"    --> Wrong depth of node 16: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "getDepth() of input sequence " + printInputSequence(arrList1) + " caused " + caughtException);
	}
		
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testFind() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		final String errorMsg = "find() failed for sequence: "+printInputSequence(arrList1)+
				" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n";

		Exception caughtException = null;
		try {
			assertEquals("5", tree.find(5), errorMsg+"    --> Node with key 5 not found or returned wrong elem: ");
			assertEquals("18",tree.find(18), errorMsg+"    --> Node with key 18 not found or returned wrong elem: ");
			assertEquals("1", tree.find(1), errorMsg+"    --> Node with key 1 not found or returned wrong elem: ");
			assertEquals("8", tree.find(8), errorMsg+"    --> Node with key 8 not found or returned wrong elem: ");
			assertEquals("14",tree.find(14), errorMsg+"    --> Node with key 14 not found or returned wrong elem: ");
			assertEquals("13",tree.find(13), errorMsg+"    --> Node with key 13 not found or returned wrong elem: ");
			assertEquals("3", tree.find(3), errorMsg+"    --> Node with key 8 not found or returned wrong elem: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "find() on input sequence " + printInputSequence(arrList1) + " caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testFindNotExistingKey() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		final String errorMsg = "find() failed for sequence: "+printInputSequence(arrList1)+
				" --> Your tree:"+this.convertTreeToString(tree.getRoot())+"\n";

		Exception caughtException = null;
		try {
			assertNull(tree.find(20), errorMsg + "    --> Not existing node with key 20 should not be found and return null: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, errorMsg + "    --> find for existing node with key 20 caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testFindInvalidKey() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		
		Exception expectedEx = null;
		try {
			tree.find(-1);
		} catch (Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "find() with -1 as argument should throw an IllegalArgumentException.");
	}
	
	@Test
	//@Timeout(value = 5000, unit = TimeUnit.MILLISECONDS)
	public void testRemove() {
		Exception caughtException = null;
		
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		final String errorMsg = "remove() failed for input sequence: "+printInputSequence(arrList1);
		try {
			System.out.println(this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(5), errorMsg+"\n    --> removing '5' returned false:"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 5\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(14), errorMsg+"\n    --> removing '14' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 14\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(8), errorMsg+"\n    --> removing '8' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14,8:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 8\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(16), errorMsg+"\n    --> removing '16' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14,8,16:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 16\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(13), errorMsg+"\n    --> removing '13' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14,8,16,13:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 13\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(1), errorMsg+"\n    --> removing '1' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14,8,16,13,1:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");

			System.out.println("removed 1\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(18), errorMsg+"\n    --> removing '18' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(isBST(tree), errorMsg+"\n    --> Your tree is no valid BST after removing the node sequence 5,14,8,16,13,18:\n"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertTrue(tree.getRoot().key != 18, "Treeroot error 18");

			System.out.println("removed 18\n" + this.convertTreeToString(tree.getRoot()));

			assertTrue(tree.remove(3), errorMsg+"\n    --> removing '3' returned false"+
					this.convertTreeToString(tree.getRoot())+"\n");
			assertNull(tree.getRoot(), errorMsg + "\n    --> Your tree should be empty after removing the node sequence 5,14,8,16,13,18,3:\n" +
					this.convertTreeToString(tree.getRoot()) + "\n");

			System.out.println("removed 3\n" + this.convertTreeToString(tree.getRoot()));
		} catch (Exception e) {
			caughtException = e;
		}
		assertNull(caughtException, errorMsg + "\n    --> removing existing nodes caused " + caughtException);
	}
	
	@Test
	public void testRemoveInvalid() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		
		Exception expectedEx = null;
		try {
			tree.remove(-1);
		} catch (Exception e) {
			expectedEx = e;
		}
		
		assertTrue(expectedEx instanceof IllegalArgumentException, "remove() with -1 as argument should throw an IllegalArgumentException but found "+expectedEx);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRemoveNotExisting() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		final String errorMsg = "remove() failed for input sequence: "+printInputSequence(arrList1);
		
		Exception caughtException = null;
		try {
			assertFalse(tree.remove(20), errorMsg+"\n    --> removal of not existing node with key '20' returned true"+
					this.convertTreeToString(tree.getRoot())+"\n");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "remove() of not existing node with key '20' caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testSizeWithRemove() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		
		final String errorMsg = "size() failed for input sequence: "+printInputSequence(arrList1);
		Exception caughtException = null;
		
		try {
			tree.remove(1); 
			assertEquals(7, tree.size(), errorMsg+"\n    --> Wrong size after removing node 1:");
			
			tree.remove(8); 
			assertEquals(6, tree.size(), errorMsg+"\n    --> Wrong size after removing node 1 and 8:");
			
			tree.remove(5); 
			assertEquals(5, tree.size(), errorMsg+"\n    --> Wrong size after removing node 1, 8 and 5:");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "size() caused " + caughtException + " after removing existing nodes.");
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testSizeWithRemoveNotExisting() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		
		final String errorMsg = "size() failed for input sequence: "+printInputSequence(arrList1);
		Exception caughtException = null;
		
		try {
			tree.remove(20); 
			assertEquals(8, tree.size(), errorMsg+"\n    --> Wrong size after removing not existing node 20:");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "size() after removing not existing node with key '20' caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testToArrayInOrder() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		Exception caughtException = null;
		
		try {
			int[] array = tree.toArrayInOrder();
			assertNotNull(array, "toArrayInOrder() returned null for tree with input sequence: "+printInputSequence(arrList1));
			
			final String errorMsg = "toArrayInOrder() is wrong for input sequence: "+printInputSequence(arrList1)
					+this.convertTreeToString(tree.getRoot())
					+"\n\n    --> Your InOrder sequence: "+this.printInputSequence(array)+": ";
			
			

			assertEquals(array[0], arrList1inorder[0], errorMsg);
			assertEquals(array[1], arrList1inorder[1], errorMsg);
			assertEquals(array[2], arrList1inorder[2], errorMsg);
			assertEquals(array[3], arrList1inorder[3], errorMsg);
			assertEquals(array[4], arrList1inorder[4], errorMsg);
			assertEquals(array[5], arrList1inorder[5], errorMsg);
			assertEquals(array[6], arrList1inorder[6], errorMsg);
			assertEquals(array[7], arrList1inorder[7], errorMsg);

		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "toArrayInOrder() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testToArrayPreOrder() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		Exception caughtException = null;
		
		try {
			int[] array = tree.toArrayPreOrder();
			assertNotNull(array, "toArrayPreOrder() returned null for tree with input sequence: "+printInputSequence(arrList1));
			
			final String errorMsg = "toArrayPreOrder() is wrong for input sequence: "+printInputSequence(arrList1)
					+this.convertTreeToString(tree.getRoot())
					+"\n\n    --> Your PreOrder sequence: "+this.printInputSequence(array)+": ";
			

			assertEquals(array[0], arrList1preorder[0], errorMsg);
			assertEquals(array[1], arrList1preorder[1], errorMsg);
			assertEquals(array[2], arrList1preorder[2], errorMsg);
			assertEquals(array[3], arrList1preorder[3], errorMsg);
			assertEquals(array[4], arrList1preorder[4], errorMsg);
			assertEquals(array[5], arrList1preorder[5], errorMsg);
			assertEquals(array[6], arrList1preorder[6], errorMsg);
			assertEquals(array[7], arrList1preorder[7], errorMsg);

		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "toArrayPreOrder() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
		
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testToArrayPostOrder() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		Exception caughtException = null;
		
		try {
			int[] array = tree.toArrayPostOrder();
			assertNotNull(array, "toArrayPostOrder() returned null for tree with input sequence: "+printInputSequence(arrList1));
			
			final String errorMsg = "toArrayPostOrder() is wrong for input sequence: "+printInputSequence(arrList1)
					+this.convertTreeToString(tree.getRoot())
					+"\n\n    --> Your PostOrder sequence: "+this.printInputSequence(array)+": ";
			

			assertEquals(array[0], arrList1postorder[0], errorMsg);
			assertEquals(array[1], arrList1postorder[1], errorMsg);
			assertEquals(array[2], arrList1postorder[2], errorMsg);
			assertEquals(array[3], arrList1postorder[3], errorMsg);
			assertEquals(array[4], arrList1postorder[4], errorMsg);
			assertEquals(array[5], arrList1postorder[5], errorMsg);
			assertEquals(array[6], arrList1postorder[6], errorMsg);
			assertEquals(array[7], arrList1postorder[7], errorMsg);

		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "toArrayPostOrder() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testGetParent() {
		IBinarySearchTree bst = createBSTfromList(arrList2);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{10,5,12, 3};
		final String errorMsg = "getParent() is wrong for input sequence: "+printInputSequence(arrList2)
			+this.convertTreeToString(tree.getRoot());
	
		Exception caughtException = null;
		try {
			assertEquals(10, tree.getParent(5), errorMsg+"\n    --> Wrong parent of node 5: ");
			assertEquals(10, tree.getParent(12), errorMsg+"\n    --> Wrong parent of node 12: ");
			assertEquals(5, tree.getParent(3), errorMsg+"\n    --> Wrong parent of node 3: ");
			assertEquals(10, tree.getParent(10), errorMsg+"\n    --> Wrong parent of node 10 (root): ");

			assertEquals(-1, tree.getParent(20), errorMsg + "\n    --> Wrong parent of not existing node 20: ");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "getParent() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList2));
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testGetParentIsRoot() {
		IBinarySearchTree bst = createBSTfromList(arrList2);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{10,5,12, 3};
		final String errorMsg = "getParent() is wrong for input sequence: "+printInputSequence(arrList2)
			+this.convertTreeToString(tree.getRoot());
		Exception caughtException = null;
		try {
			assertEquals(10, tree.getParent(10), errorMsg+"\n    --> Wrong parent of node 10 (root): ");
		}catch(Exception ex) {
			caughtException = ex;
		}

		assertNull(caughtException, errorMsg + "\n    --> Parent of node 10 (root) caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsRoot() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		final String errorMsg = "isRoot() is wrong for input sequence: "+printInputSequence(arrList1)
			+this.convertTreeToString(tree.getRoot());
		Exception caughtException = null;
		
		try {
			assertTrue(tree.isRoot(5), errorMsg+"\n    --> isRoot(5) which is the root returns false");
			assertFalse(tree.isRoot(18), errorMsg+"\n    --> isRoot(18) which is not the root returns true");
			assertFalse(tree.isRoot(1), errorMsg+"\n    --> isRoot(1) which is not the root returns true");
			assertFalse(tree.isRoot(8), errorMsg+"\n    --> isRoot(8) which is not the root returns true");
			assertFalse(tree.isRoot(14), errorMsg+"\n    --> isRoot(14) which is not the root returns true");
			assertFalse(tree.isRoot(16), errorMsg+"\n    --> isRoot(16) which is not the root returns true");
			assertFalse(tree.isRoot(13), errorMsg+"\n    --> isRoot(13) which is not the root returns true");
			assertFalse(tree.isRoot(3), errorMsg+"\n    --> isRoot(3) which is not the root returns true");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "isRoot() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsRootNotExisting() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		final String errorMsg = "isRoot() is wrong for input sequence: "+printInputSequence(arrList1)
			+this.convertTreeToString(tree.getRoot());
		Exception caughtException = null;
		
		try {
			assertFalse(tree.isRoot(20), errorMsg+"\n    --> isRoot() on not existing node 20 returns true");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "isRoot() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsRootInvalid() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());
		
		Exception expectedEx = null;
		try {
			tree.isRoot(-1);
		} catch(Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "isRoot() with -1 as argument should throw an IllegalArgumentException but found: "+expectedEx);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsInternal() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		final String errorMsg = "isInternal() is wrong for input sequence: "+printInputSequence(arrList1)
			+this.convertTreeToString(tree.getRoot());
		
		Exception caughtException = null;
		
		try {
			assertTrue(tree.isInternal(5), errorMsg+"\n    --> Found isInternal(5) == false");
			assertTrue(tree.isInternal(18), errorMsg+"\n    --> Found isInternal(18) == false");
			assertTrue(tree.isInternal(1), errorMsg+"\n    --> Found isInternal(1) == false");
			assertTrue(tree.isInternal(8), errorMsg+"\n    --> Found isInternal(8) == false");
			assertTrue(tree.isInternal(14), errorMsg+"\n    --> Found isInternal(14) == false");
			assertFalse(tree.isInternal(16), errorMsg+"\n    --> Found isInternal(16) == true");
			assertFalse(tree.isInternal(13), errorMsg+"\n    --> Found isInternal(13) == true");
			assertFalse(tree.isInternal(3), errorMsg+"\n    --> Found isInternal(3) == true");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "isInternal() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsInternalInvalid() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		
		Exception expectedEx = null;
		try {
			tree.isInternal(-1);
		} catch(Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "isInternal() with -1 as argument should throw an IllegalArgumentException but found: "+expectedEx);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsExternal() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		final String errorMsg = "isExternal() is wrong for input sequence: "+printInputSequence(arrList1)
			+this.convertTreeToString(tree.getRoot());
		
		Exception caughtException = null;
		try {
			assertFalse(tree.isExternal(5), errorMsg+"\n    --> Found isExternal(5) == true");
			assertFalse(tree.isExternal(18), errorMsg+"\n    --> Found isExternal(18) == true");
			assertFalse(tree.isExternal(1), errorMsg+"\n    --> Found isExternal(1) == true");
			assertFalse(tree.isExternal(8), errorMsg+"\n    --> Found isExternal(8) == true");
			assertFalse(tree.isExternal(14), errorMsg+"\n    --> Found isExternal(14) == true");
			assertTrue(tree.isExternal(16), errorMsg+"\n    --> Found isExternal(16) == false");
			assertTrue(tree.isExternal(13), errorMsg+"\n    --> Found isExternal(13) == false");
			assertTrue(tree.isExternal(3), errorMsg+"\n    --> Found isExternal(3) == false");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "isExternal() caused " + caughtException + " for tree with input sequence: " + printInputSequence(arrList1));
	}

	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsExternalInvalid() {
		IBinarySearchTree bst = createBSTfromList(arrList1);	//{5, 18, 1, 8, 14, 16, 13, 3};
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	
		
		Exception expectedEx = null;
		try {
			tree.isExternal(-1);
		} catch(Exception e) {
			expectedEx = e;
		}
		assertTrue(expectedEx instanceof IllegalArgumentException, "isExternal() with -1 as argument should throw an IllegalArgumentException but found: "+expectedEx);
	}

	@Test
	@Timeout(value = 5000, unit = TimeUnit.MILLISECONDS)
	public void testRuntimeComparisonCheckBSTWithPreGenList() {
		ArrayList<Integer> testList = null;
		try {
			testList = createTestListFromFile("src/testListWithoutDuplicates.txt");

		} catch(Exception ex) {
			assertNull(ex, "testRuntimeComparisonCheckBSTWithPreGenList() could not be tested as testfile could not be loaded. Pls check path and test again.");
		}
		assertNotNull(testList, "testRuntimeComparisonCheckBSTWithPreGenList() could not be tested as testfile could not be loaded. Pls check path and test again.");
						
		// start with an empty key as runtimeComparison() shall create a binary search tree based on the given list.
		tree = new MyBinarySearchTree();
		
		// Worst case is the search for the last key in the list
		int key = testList.get(testList.size()-1);
		
		Exception caughtException = null;
		try {
			int[] result = tree.runtimeComparison(testList, key);
			
			assertNotNull(result, "runtimeComparison() returns null for correct given list+key.");
			assertEquals(53,result[0], "runtimeComparison() returns wrong number of comparisons for searching the last key of a given list in a BST with 1000000 elements: ");	// check BST
			
		} catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "runtimeComparison() for correct given list+key caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 5000, unit = TimeUnit.MILLISECONDS)
	public void testRuntimeComparisonCheckListWithPreGenList() {
		ArrayList<Integer> testList = null;
		try {
			//testList = createTestListFromFile("src/"+inputFilePath+ "/assignment04/testListWithoutDuplicates.txt");
			testList = createTestListFromFile("src/testListWithoutDuplicates.txt");
		} catch(Exception ex) {
			assertNull(ex, "testRuntimeComparisonCheckListWithPreGenList() could not be tested as testfile could not be loaded. Pls check path and test again.");
		}
		assertNotNull(testList, "testRuntimeComparisonCheckListWithPreGenList() could not be tested as testfile could not be loaded. Pls check path and test again.");
						
		// start with an empty key as runtimeComparison() shall create a binary search tree based on the given list.
		tree = new MyBinarySearchTree();
		
		// Worst case is the search for the last key in the list
		int key = testList.get(testList.size()-1);
		
		Exception caughtException = null;
		try {
			int[] result = tree.runtimeComparison(testList, key);
			assertNotNull(result, "runtimeComparison() returns null for correct given list+key.");
			assertEquals(testList.size(),result[1], "runtimeComparison() returns wrong number of comparisons for searching the last key in a list with 1000000 elements: ");	// check list
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "runtimeComparison() for correct given list+key caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRuntimeComparisonAssignmentExampleBSTcheck() {
		ArrayList<Integer> testList = new ArrayList<Integer>();
		testList.add(8);
		testList.add(17);
		testList.add(10);
		testList.add(3);
		testList.add(1);
		
		// start with an empty key as runtimeComparison() shall create a binary search tree based on the given list.
		tree = new MyBinarySearchTree();
		
		int key = 3;
		Exception caughtException = null;
		try {
			int[] result = tree.runtimeComparison(testList, key);
			assertNotNull(result, "runtimeComparison() returns null for correct given list+key.");
			assertEquals(3, result[0], "runtimeComparison() returns wrong number of comparisons for searching key '3' in a BST based on the list sequence: 8,17,10,3,1");	// check BST
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "runtimeComparison() for correct given list+key caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRuntimeComparisonAssignmentExampleListcheck() {
		ArrayList<Integer> testList = new ArrayList<Integer>();
		testList.add(8);
		testList.add(17);
		testList.add(10);
		testList.add(3);
		testList.add(1);
		
		// start with an empty tree as runtimeComparison() shall create a binary search tree based on the given list.
		tree = new MyBinarySearchTree();
		
		int key = 3;
		Exception caughtException = null;
		try {
			int[] result = tree.runtimeComparison(testList, key);
			assertNotNull(result, "runtimeComparison() returns null for correct given list+key.");
			assertEquals(4, result[1], "runtimeComparison() returns wrong number of comparisons for searching key '3' in a list based on the sequence: 8,17,10,3,1");	// check list
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "runtimeComparison() for correct given list+key caused " + caughtException);
	}
	
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testRuntimeComparisonSortedList() {
		tree = new MyBinarySearchTree();
	
		ArrayList<Integer> testList = new ArrayList<Integer>();
		int numOfKeys = 10;
		int key =numOfKeys-1;
		
		// generate list and tree
		for (int i = 0; i < numOfKeys; i++) {
			testList.add(i);
			tree.insert(i, Integer.valueOf(i).toString());
		}
		
		Exception caughtException = null;
		try {
			int[] result = tree.runtimeComparison(testList, key);
			assertNotNull(result, "runtimeComparison() returns null for correct given list+key.");
			assertEquals((testList.size())*2-1, result[0], "runtimeComparison() returns wrong number of comparisons for search key 9 in a BST based on the sequence: 0,1,2,3,4,5,6,7,8,9: ");
			assertEquals((testList.size()), result[1], "runtimeComparison() returns wrong number of comparisons for search key 9 in a list based on the sequence: 0,1,2,3,4,5,6,7,8,9: ");
		}catch (Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "runtimeComparison() for correct given list+key caused " + caughtException);
		
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsBSTtrue() {
		tree = new MyBinarySearchTree();
		
		final int[] arr = {13, 5, 18, 1, 8, 14, 16, 13, 3};
		IBinarySearchTree bst = createBSTfromList(arr);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	

		final String errorMsg = "isBST() is wrong for input sequence: "+printInputSequence(arr)
			+this.convertTreeToString(tree.getRoot());
	
		Exception caughtException = null;
		try {
			assertTrue(tree.isBST(tree), errorMsg+"\n    --> isBST should return true but was false.");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, errorMsg + "\n    --> caused " + caughtException);
	}
	
	@Test
	@Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
	public void testIsBSTfalse() {
		
		BinaryTreeNode root13= new BinaryTreeNode(13,"13");
		BinaryTreeNode node5 = new BinaryTreeNode(5,"5");
		BinaryTreeNode node18= new BinaryTreeNode(18,"18");
		BinaryTreeNode node1 = new BinaryTreeNode(1,"1");
		BinaryTreeNode node8 = new BinaryTreeNode(8,"8");
		BinaryTreeNode node14= new BinaryTreeNode(14,"14");
		BinaryTreeNode node16= new BinaryTreeNode(16,"16");
		BinaryTreeNode node13= new BinaryTreeNode(13,"13");
		BinaryTreeNode node3 = new BinaryTreeNode(3,"3");
		
		root13.left = node5; 
		root13.right= node18;
		node5.left= node1;
		node5.right=node8;
		node1.right=node3;
		node8.right=node13;
		node18.left=node14;
		//node14.right=node16;
		node13.right=node16;
		
		
		tree = new MyBinarySearchTree(root13, 9);
				
		final String errorMsg = "isBST() is wrong for the tree: "
			+this.convertTreeToString(tree.getRoot());

		Exception caughtException = null;
		try {
			assertFalse(tree.isBST(tree), errorMsg+"\n    --> isBST should return false (node 16 is placed incorrectly here) but was true.");
		}catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, errorMsg + "\n    --> caused " + caughtException);
	}
	

	@Test
	@Timeout(value=500, unit = TimeUnit.MILLISECONDS)
	public void testReturnMinKey() {
		IBinarySearchTree bst = createBSTfromList(arrList1);
		tree = new MyBinarySearchTree(bst.getRoot(), bst.size());	//{5, 18, 1, 8, 14, 16, 13, 3};
		Exception caughtException = null;
		try {
			String result = tree.returnMinKey();
			
			assertNotNull(result, "returnMinKey() returned null called on correct tree tree with input sequence: "
					+printInputSequence(arrList1));
			
			final String errorMsg = "returnMinKey() is wrong for tree with input sequence: "+printInputSequence(arrList1)
				+this.convertTreeToString(tree.getRoot());

			assertEquals(0, result.compareTo("1"), errorMsg + "\n    --> should return elem of node with key 1: in this case expected \"1\", but returned \"" + result + "\"");
		} catch(Exception ex) {
			caughtException = ex;
		}
		assertNull(caughtException, "returnMinKey() on tree with input sequence: " + printInputSequence(arrList1)
				+ "\n    -->caused " + caughtException);
	}

	

	/******************************************************************************************************
	 * PRIVATE METHODS
	 * 
	 */
	
	private IBinarySearchTree createBSTfromList(int[] list) {
		MyBinarySearchTree bst = new MyBinarySearchTree();
		
		for(int key : list) {
			bst.insert(key, String.valueOf(key));
		}
		return bst;
	}
	

	private String convertTreeToString(BinaryTreeNode root) {
		if(root == null) return null;
		
		StringBuilder sbTree = null;
		
		sbTree = convertTreeToStringBuilder(root);
		if(sbTree != null) {
			return sbTree.toString();
		} else {
			return null;
		}
	}
	
	private String printInputSequence(int[] arr) {
		StringBuilder sb = new StringBuilder(arr.length);
		
		for(Integer i: arr) {
			sb.append(i);
			sb.append(',');
		}
		sb.deleteCharAt(sb.lastIndexOf(","));
		
		return sb.toString();
	}
	
	private String printInputSequence(Object[] arr) {
		StringBuilder sb = new StringBuilder(arr.length);
		
		for(Object i: arr) {
			if(i instanceof Integer) {
				sb.append(i);
			} else {
				sb.append((String)i);
			}
				sb.append(',');
		}
		sb.deleteCharAt(sb.lastIndexOf(","));
		
		return sb.toString();
	}
	
	private StringBuilder convertTreeToStringBuilder(BinaryTreeNode root) {
		visitedNodes.clear();
		if (root == null) return null;
        final int height = 5, width = 64;
 
        int len = width * height * 2 + 2;
        StringBuilder sb = new StringBuilder(len);
        for (int i = 1; i <= len; i++)
            sb.append(i < len - 2 && i % width == 0 ? "\n" : ' ');
 
        displayR(sb, width / 2, 1, width / 4, width, root, " ");
        //System.out.println(sb);
        return sb;
    }
 
	private ArrayList<BinaryTreeNode> visitedNodes = new ArrayList<BinaryTreeNode>();
    private void displayR(StringBuilder sb, int c, int r, int d, int w, BinaryTreeNode n,
            String edge) {
        if (n != null) {
        	////////////////////////////////////////////////////
        	// This code part is used to avoid infinite loops because of wrong node links!
           	if(visitedNodes.contains(n)) {
	        		String s = String.valueOf(n.key);
	                int idx1 = r * w + c - (s.length() + 1) / 2;
	                int idx2 = idx1 + s.length();
	                int idx3 = idx1 - w;
	                if (idx2 < sb.length())
	                    sb.replace(idx1, idx2, "("+s+")").replace(idx3, idx3 + 2, edge);
        			
        			return;
        		}
        	else {
        		visitedNodes.add(n);
        	}
           	////////////////////////////////////////////////////
           	
            displayR(sb, c - d, r + 2, d / 2, w, n.left, " /");
 
            String s = String.valueOf(n.key);
            int idx1 = r * w + c - (s.length() + 1) / 2;
            int idx2 = idx1 + s.length();
            int idx3 = idx1 - w;
            if (idx2 < sb.length())
                sb.replace(idx1, idx2, s).replace(idx3, idx3 + 2, edge);
 

            displayR(sb, c + d, r + 2, d / 2, w, n.right, "\\ ");
        }
    }

    
    private ArrayList<Integer> createTestListFromFile(String filename){
    	try {
    		if (filename == null) return null;
	    	File file = new File(filename); 
	    	  
	    	BufferedReader br = new BufferedReader(new FileReader(file)); 
	    	String line = null;
	    	ArrayList<Integer> list = new ArrayList<Integer>();
	    	
	    	while ((line = br.readLine()) != null) {
	    		list.add(Integer.valueOf(line)); 
	    	} 
	    	
	    	return list;
    	} catch (Exception ex) {return null;}
    }
    
    private boolean isBST(IBinarySearchTree bst) throws IllegalArgumentException{
		if (bst == null) throw new IllegalArgumentException();
		
		BinaryTreeNode root = bst.getRoot();
		if(root == null) throw new IllegalArgumentException();
		
		if(root.left != null) {
			if(root.left.key > root.key) return false;
		}
		
		if(root.right != null) {
			if(root.right.key < root.key) return false; 
		}
		
		return checkLeftSubTree(root.left, root) && checkRightSubTree(root.right, root);
	}
    
	private boolean checkLeftSubTree(BinaryTreeNode n, BinaryTreeNode root) {
		boolean left = true;
		boolean right= true;
		
		if(n == null) return true;
			
		if(n.left != null) {
			if (n.left.key <= n.key && n.left.key <= root.key) {
				left = checkLeftSubTree(n.left, root);
			} else return false;
		} 
	
		if(n.right != null) {
			if(n.right.key > n.key && n.right.key <= root.key) {
				right = checkLeftSubTree(n.right, root);
			} else return false;
		}
		
		return left&&right;
	}
	
	private boolean checkRightSubTree(BinaryTreeNode n, BinaryTreeNode root) {
		boolean left = true;
		boolean right= true;
		
		if(n == null) return true;
		
		if(n.left != null) {
			if (n.left.key <= n.key && n.left.key > root.key) {
				left = checkRightSubTree(n.left, root);
			} else return false;
		} 
	
		if(n.right != null) {
			if(n.right.key > n.key && n.right.key > root.key) {
				right = checkRightSubTree(n.right, root);
			} else return false;
		}
		
		return left&&right;
	}
	
}
