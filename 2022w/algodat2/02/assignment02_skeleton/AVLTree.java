package assignment02;

import java.util.function.Function;

public class AVLTree implements IAVLTree {

	private AVLNode root;
	private int size;

	
	/**
	 * Default constructor. Initializes the AVL tree.
	 */
	public AVLTree() {
		root = null;
	}

	/**
	 * @returns the root of the AVLTree
	 */
	public AVLNode getTreeRoot() {
		return root;
	}
	
	/**
	 * Retrieves tree height.
	 * 
	 * @return -1 in case of empty tree, current tree height otherwise.
	 */
	public int getTreeHeight() {
		if (root == null) {
			return -1;
		} else {
			return root.height;
		}
	}

	/**
	 * Yields number of key/value pairs in the tree.
	 *
	 * @return Number of key/value pairs.
	 */
	public int getSize() {
		return size;
	}

	/**
	 * Yields an array representation of the tree (pre-order).
	 *
	 * @return Array representation of the tree.
	 */
	public float[] toArray() {
		float[] array = new float[size];

		toArrayPreOrder(root, array, 0);

		return array;
	}

	/**
	 * Returns value of node with given key.
	 *
	 * @param key  Key to search.
	 * @return 	  Corresponding value if key was found, -1 otherwise.
	 */
	public float findByKey(int key) {
		AVLNode node =  bstFindByKey(key, root);

		return node == null ? -1 : node.value;
	}

	/**
	 * Inserts a new node into AVL tree.
	 *
	 * @param key Key of the new node.
	 * @param value Data of the new node. Must be >= 0.
	 * @return   Nodes with the same key are not allowed. In this case false is returned. Otherwise true.
	 */
	public boolean insert(int key, float value) {
		AVLNode node = new AVLNode(key, value);

		if (!bstInsert(node, root)) {
			return false;
		}

		updateHeights(node);

		for (AVLNode cur = node.parent; cur != null; cur = cur.parent) {
			AVLNode parent = cur.parent;
			AVLNode grandparent = parent.parent;

			if (!isBalanced(grandparent)) {
				rebalance(cur, parent, grandparent);
			}
		}

		size++;

		return true;
	}

	/**
	 * Removes node with given key.
	 *
	 * @param key Key of node to remove.
	 * @return true if node was found and deleted.
	 */
	public boolean removeByKey(int key) {
		AVLNode node = bstFindByKey(key, root);

		if (node == null) {
			return false;
		}

		bstRemoveNode(node);

		updateHeights(root);

		for (AVLNode cur = node.parent; cur != null; cur = cur.parent) {
			AVLNode parent = cur.parent;
			AVLNode grandparent = parent.parent;

			if (!isBalanced(grandparent)) {
				rebalance(cur, parent, grandparent);
			}
		}

		size--;

		return true;
	}
	
	// Write any other private helper method you might find helpful
	// For example: getComponents(), isBalanced(), etc.

	private void toArrayPreOrder(AVLNode node, float[] array, int index) {
		if (node == null) {
			return;
		}

		array[index] = node.value;

		toArrayPreOrder(node.left, array,  2 * index + 1);
		toArrayPreOrder(node.right, array, 2 * index + 2);
	}

	private AVLNode bstFindByKey(float key, AVLNode subRoot) {
		if (subRoot == null) {
			return null;
		} else if (subRoot.key == key) {
			return subRoot;
		} else if (subRoot.key > key) {
			return bstFindByKey(key, subRoot.left);
		} else {
			return bstFindByKey(key, subRoot.right);
		}
	}

	// insert a node, not caring about balancing.
	private boolean bstInsert(AVLNode node, AVLNode subRoot) {
		if (node == null) {
			return false;
		}

		if (node.key < subRoot.key) {
			if (subRoot.left == null) {
				subRoot.left = node;
				node.parent = subRoot;
			} else {
				return bstInsert(node, subRoot.left);
			}
		} else if (node.key > subRoot.key) {
			if (subRoot.right == null) {
				subRoot.right = node;
				node.parent = subRoot;
			} else {
				return bstInsert(node, subRoot.right);
			}
		} else {
			return false;
		}

		return true;
	}

	private void bstRemoveNode(AVLNode node) {
		if (node == null) {
			return;
		}

		if (node.left == null && node.right == null) {
			if (node.parent.left == node) {
				node.parent.left = null;
			} else {
				node.parent.right = null;
			}
		} else if (node.left == null) {
			node.right.parent = node.parent;
			if (node.parent.left == node) {
				node.parent.left = node.right;
			} else {
				node.parent.right = node.right;
			}
		} else if (node.right == null) {
			node.left.parent = node.parent;
			if (node.parent.left == node) {
				node.parent.left = node.left;
			} else {
				node.parent.right = node.left;
			}
		} else {
			AVLNode successor = node.right;
			while (successor.left != null) {
				successor = successor.left;
			}

			node.key = successor.key;
			node.value = successor.value;

			if (successor.parent.left == successor) {
				successor.parent.left = successor.right;
			} else {
				successor.parent.right = successor.right;
			}
		}
	}

	// go up the tree from the given subroot and update heights
	private void updateHeights(AVLNode subRoot) {
		for (AVLNode node = subRoot; node != null; node = node.parent) {
			node.height = Math.max(node.left == null ? 0 : node.left.height,
					node.right == null ? 0 : node.right.height) + 1;
		}
	}

	// get balance = left.height - right.height; negative means right heavy, positive means left heavy
	private int getBalance(AVLNode subRoot) {
		return (subRoot.left == null ? 0 : subRoot.left.height)
				- (subRoot.right == null ? 0 : subRoot.right.height);
	}

	// check whether a given subtree is balanced
	private boolean isBalanced(AVLNode subRoot) {
		return Math.abs(getBalance(subRoot)) <= 1;
	}

	// rebalance based on the given structure
	private void rebalance(AVLNode node, AVLNode parent, AVLNode grandparent) {
		// get cut&link components
		AVLNode[] components = new AVLNode[7];

		// a, b, c
		components[1] = node;
		components[3] = parent;
		components[5] = grandparent;

		// t0, t1, t2, t3
		components[0] = parent == grandparent.left ? grandparent.right : grandparent.left;
		components[2] = node == parent.left ? parent.right : parent.left;
		components[4] = node.left;
		components[6] = node.right;

		// relink components

		// set c[4] to be the new (sub)root
		if (grandparent == root) {
			root = components[3];
		} else {
			grandparent.parent = components[3];
		}

		// set children of new subroot
		components[3].left = components[1];
		components[3].right = components[5];

		// set children of left child of subroot
		components[1].left = components[0];
		components[1].right = components[2];

		// set children of right child of subroot
		components[5].left = components[4];
		components[5].right = components[6];
	}
}
