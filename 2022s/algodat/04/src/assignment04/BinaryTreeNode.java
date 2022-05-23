package assignment04;

public class BinaryTreeNode {
	/**
	 * Reference to the left child node
	 */
	public BinaryTreeNode left;
	
	/**
	 * Reference to the right child node
	 */
	public BinaryTreeNode right;
	
	/**
	 * Reference to the parent node
	 */
	public BinaryTreeNode parent;
	
	/**
	 * Key of the node
	 */
	public Integer key;
	
	/**
	 * Data of the node
	 */
	public String elem;
	
	public BinaryTreeNode(Integer key, String elem) {
		this.key = key;
		this.elem = elem;
		left = null;
		right = null;
	}
}