package assignment04;

import java.util.ArrayList;


public interface IBinarySearchTree {
	/**
	 * Returns the root of your binary search tree, or null if the tree is empty.
	 * 
	 * @return root of the binary search tree
	 */
	public BinaryTreeNode getRoot();
	
	/**
	 * Insert the element elem into the binary search tree.
 	 * Null-objects (elem) and keys < 0 are not allowed, in this case an exception is thrown.
 	 * 
	 * @param key, elem
	 * @throws IllegalArgumentException if elem is null or key is < 0.
	 */
	public void insert(int key, String elem) throws IllegalArgumentException;
	
	/**
	 * Returns the element of the node found with the given key, or null if key was not found.
	 * 
	 * @param key
	 * @return The corresponding element of the node with the given key, or null if key was not found.
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public String find(int key) throws IllegalArgumentException;
	
	/**
	 * Removes the node with the given key, and returns true if element was found AND removed.
	 * 
	 * @param key
	 * @return success
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public boolean remove(int key) throws IllegalArgumentException;
	
	/**
	 * @return Returns the number of elements stored in the tree.
	 */
	public int size();	
	
	/**
	 * @return Returns an array-representation of the stored keys (Postorder traversal).
	 */
	public int[] toArrayPostOrder();
	
	/**
	 * @return Returns an array-representation of the stored keys (Inorder traversal).
	 */
	public int[] toArrayInOrder();
	
	/**
	 * @return Returns an array-representation of the stored keys (Preorder traversal).
	 */
	public int[] toArrayPreOrder();
	
	/**
	 * Search the parent node of the node with the given key,
     * and return its key (or -1 if not found). If the node with the given key is the root,
     * then return the key of the root.
     * 
	 * @param key
	 * @return key of parent
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public int getParent(int key) throws IllegalArgumentException;
	
	/**
	 * @param key
	 * @return true if the node with the given key is the root, false otherwise.
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public boolean isRoot(int key) throws IllegalArgumentException;
	
	/**
	 * @param key
	 * @return Return true if the node with the given key is an internal node, otherwise return false
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public boolean isInternal(int key) throws IllegalArgumentException;
	
	/**
	 * @param key
	 * @return Return true if the node with the given key is an external node, otherwise return false.
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public boolean isExternal(int key) throws IllegalArgumentException;
	
	/**
	 * This method verifies a given BinaryTree, if it is a correct Binary Search Tree.
	 * 
	 * @param bst represents a binary search tree
	 * @return true if the tree passed as a parameter is a valid Binary Search Tree, false otherwise. 
	 * @throws IllegalArgumentException if bst is null
	 */
	public boolean isBST(IBinarySearchTree bst) throws IllegalArgumentException;
	
	/**
	 * Search the node with the minimum key in the entire binary search tree and return its element.
	 * 
	 * @return the element of the minimum key
	 */
	public String returnMinKey();
	
	/**
	 * Creates a binary search tree based on the given (linear) list and then determines the number of 
	 * comparisons necessary to search a key in both, the internal BST and in the list. This numbers 
	 * shall be returned.
	 * 
	 * @param list 
	 * @param key The key to be searched in list and BST.
	 * @return The number of comparisons needed to find the given key (1) in the BST and (2) in the list in form of
	 * 		   an int[] array of size 2 (index 0 contains BST comparisons, index 1 contains list comparisons).
	 * @throws IllegalArgumentException if list is null or key is < 0.
	 */
	public int[] runtimeComparison(ArrayList<Integer> list, int key) throws IllegalArgumentException;
	
	/**
	 * Determines the depth of a node in the tree. 
	 * 
	 * @param key The key of the node of which the depth should be determined.
	 * @return The depth of the node with given key. If the key is not found return -1.
	 * @throws IllegalArgumentException if key is < 0.
	 */
	public int getDepth(int key) throws IllegalArgumentException;
	
	/**
	 * This method analyses the tree and determines if it is a complete binary tree.
	 * 
	 * @return True if the tree is complete, false otherwise. In case the tree is empty return false as well.
	 */
	//public boolean isTreeComplete();
}
