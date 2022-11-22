package assignment02;

import java.util.ArrayList;
import java.util.Objects;

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
	 * @return the root of the AVLTree
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
		return root == null ? -1 : root.height;
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
		// todo: this is terrible

		ArrayList<Float> list = new ArrayList<>();

		recPreOrder(root, list);

		float[] array = new float[list.size()];

		for (int i = 0; i < list.size(); i++) {
			array[i] = list.get(i);
		}

		return array;
	}

	/**
	 * Returns value of node with given key.
	 *
	 * @param key  Key to search.
	 * @return 	  Corresponding value if key was found, -1 otherwise.
	 */
	public float findByKey(int key) {
		AVLNode n = findNode(key);

		return n == null ? -1 : findNode(key).value;
	}

	/**
	 * Inserts a new node into AVL tree.
	 *
	 * @param key Key of the new node.
	 * @param value Data of the new node. Must be >= 0.
	 * @return   Nodes with the same key are not allowed. In this case false is returned. Otherwise true.
	 */
	public boolean insert(int key, float value) {
		AVLNode n = new AVLNode(key, value);

		if (root == null) {
			n.height = 0;
			root = n;
			size++;

			return true;
		}

		if (!bstInsert(root, n)) {
			return false;
		}

		size++;

		fixHeights(root);

		if (n.parent == null || n.parent.parent == null) {
			return true;
		}

		AVLNode x = n;
		AVLNode y = x.parent;
		AVLNode z = y.parent;

		// go up until we find a node x whose grandparent z is unbalanced
		while (z != null) {
			if (!isBalanced(z)) {
				break;
			}

			x = y;
			y = z;
			z = z.parent;
		}

		// node doesn't have an unbalanced grandparent, nothing to do
		if (z == null) {
			return true;
		}

		rebalance(x, y, z);

		fixHeights(root);

		return true;
	}

	/**
	 * Removes node with given key.
	 *
	 * @param key Key of node to remove.
	 * @return true if node was found and deleted.
	 */
	public boolean removeByKey(int key) {
		// todo: something in here is broken

		AVLNode n = findNode(key);

		if (n == null) {
			return false;
		}

		AVLNode successor = bstRemove(n);

		size--;

		fixHeights(root);

		AVLNode z = successor == null ? n.parent : successor.parent;

		while (z != null) {
			if (!isBalanced(z)) {
				boolean zLeftHigher = z.left != null && (z.right == null || z.left.height > z.right.height);
				AVLNode y = zLeftHigher ? z.left : z.right;

				boolean yLeftHigher = y.left != null && (y.right == null || y.left.height > y.right.height);
				AVLNode x = yLeftHigher ? y.left : y.right;

				rebalance(x, y, z);
			}

			z = z.parent;
		}

		fixHeights(root);

		return true;
	}
	
	// Write any other private helper method you might find helpful
	// For example: getComponents(), isBalanced(), etc.

	// get the height of a given (sub)tree
	private int getHeight(AVLNode subRoot) {
		if (subRoot == null) {
			return -1;
		}

		int leftHeight = getHeight(subRoot.left);
		int rightHeight = getHeight(subRoot.right);

		return Math.max(leftHeight, rightHeight) + 1;
	}

	// fix all heights of a given (sub)tree
	private void fixHeights(AVLNode subRoot) {
		if (subRoot == null) {
			return;
		}

		subRoot.height = getHeight(subRoot);

		fixHeights(subRoot.left);
		fixHeights(subRoot.right);
	}

	private boolean bstInsert(AVLNode subRoot, AVLNode newNode) {
		while (subRoot != null) {
			if (subRoot.key == newNode.key) {
				return false;
			} else if (subRoot.key > newNode.key) {
				if (subRoot.left == null) {
					subRoot.left = newNode;
					newNode.parent = subRoot;
					return true;
				} else {
					subRoot = subRoot.left;
				}
			} else {
				if (subRoot.right == null) {
					subRoot.right = newNode;
					newNode.parent = subRoot;
					return true;
				} else {
					subRoot = subRoot.right;
				}
			}
		}

		return false;
	}

	private AVLNode findNode(int key) {
		AVLNode n = root;

		while (n != null && n.key != key) {
			n = key < n.key ? n.left : n.right;
		}

		return n;
	}

	private AVLNode findMinimumNode(AVLNode n) {
		while (n.left != null) {
			n = n.left;
		}

		return n;
	}

	// returns the node that was removed (inorder successor if applicable, n otherwise)
	private AVLNode bstRemove(AVLNode n) {
		AVLNode successor = null;

		if (n.left == null && n.right == null) {
			// n has no children

			if (n == root) {
				root = null;
				return successor;
			}

			if (n.parent.left == n) {
				n.parent.left = null;
			} else {
				n.parent.right = null;
			}
		} else if (n.left == null) {
			// n only has a child on the right

			if (n == root) {
				root = n.right;
				return successor;
			}

			if (n.parent.left == n) {
				n.parent.left = n.right;
			} else {
				n.parent.right = n.right;
			}

			n.right.parent = n.parent;
		} else if (n.right == null) {
			// n only has a child on the left

			if (n == root) {
				root = n.left;
				root.height = 0;
				return successor;
			}

			if (n.parent.left == n) {
				n.parent.left = n.left;
			} else {
				n.parent.right = n.left;
			}

			n.left.parent = n.parent;
		} else {
			// n has two children. the minimum value in the right subtree is the (in-order) successor

			successor = findMinimumNode(n.right);

			// remove the successor from the tree
			bstRemove(successor);
			// replace the item to be deleted with the successor
			n.value = successor.value;
			n.key = successor.key;
		}

		return successor;
	}

	// get balance = left.height - right.height; negative means right heavy, positive means left heavy
	private int getBalance(AVLNode subRoot) {
		return (subRoot.left == null ? -1 : subRoot.left.height)
				- (subRoot.right == null ? -1 : subRoot.right.height);
	}

	// check whether a given subtree is balanced
	private boolean isBalanced(AVLNode subRoot) {
		return Math.abs(getBalance(subRoot)) <= 1;
	}

	private void rebalance(AVLNode x, AVLNode y, AVLNode z) {
		if (x == null || y == null || z == null) {
			return;
		}

		// get components

		AVLNode a = null, b = null, c = null;
		AVLNode[] components = new AVLNode[4];

		if (y == z.left) {	// left rotation
			if (x == y.left) {	// double rotation
				a = x;
				b = y;
				c = z;
				components[0] = a.left;
				components[1] = a.right;
				components[2] = b.right;
				components[3] = c.right;
			} else {			// single rotation
				a = y;
				b = x;
				c = z;
				components[0] = a.left;
				components[1] = b.left;
				components[2] = b.right;
				components[3] = c.right;
			}
		} else {			// right rotation
			if (x == y.left) {	// double rotation
				a = z;
				b = x;
				c = y;
				components[0] = a.left;
				components[1] = b.left;
				components[2] = b.right;
				components[3] = c.right;
			} else {			// single rotation
				a = z;
				b = y;
				c = x;
				components[0] = a.left;
				components[1] = b.left;
				components[2] = c.left;
				components[3] = c.right;
			}
		}

		// replace z with b
		if (z.parent == null) {
			root = b;
			b.parent = null;
		} else {
			if (z.parent.left == z) {
				z.parent.left = b;
			} else {
				z.parent.right = b;
			}

			b.parent = z.parent;
		}

		// set b's children
		b.left = a;
		a.parent = b;
		b.right = c;
		c.parent = b;

		// set a's children
		a.right = components[1];
		if (components[1] != null) {
			components[1].parent = a;
		}

		// set c's children
		c.left = components[2];
		if (components[2] != null) {
			components[2].parent = c;
		}
	}

	private void recPreOrder(AVLNode node, ArrayList<Float> list) {
		if (node == null) {
			return;
		}

		list.add(node.value);

		recPreOrder(node.left, list);
		recPreOrder(node.right, list);
	}
}
