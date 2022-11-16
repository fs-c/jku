package assignment02;

public interface IAVLTree {
	
	/**
	 * @return the root of the AVLTree
	 */
	public AVLNode getTreeRoot();
	
	/**
	 * Retrieves tree height.
	 * 
	 * @return -1 in case of empty tree, current tree height otherwise.
	 */
	public int getTreeHeight();
	
	
	/**
	 * Yields number of key/value pairs in the tree.
	 * 
	 * @return Number of key/value pairs.
	 */
	public int getSize();
	
	
	/**
	 * Yields an array representation of the tree (pre-order).
	 * 
	 * @return Array representation of the tree.
	 */
	public float[] toArray();
	
	
	/**
	 * Returns value of node with given key.
	 * 
	 * @param key  Key to search.
	 * @return 	  Corresponding value if key was found, -1 otherwise.
	 */
	public float findByKey(int key);
	
	
	/**
	 * Inserts a new node into AVL tree.
	 * 
	 * @param key Key of the new node.
	 * @param value Data of the new node. Must be >= 0.
	 * @return   Nodes with the same key are not allowed. In this case false is returned. Otherwise true.
	 */
	public boolean insert(int key, float value);
	
	
	/**
	 * Removes node with given key.
	 * 
	 * @param key Key of node to remove.
	 * @return true if node was found and deleted.
	 */
	public boolean removeByKey(int key);
}
