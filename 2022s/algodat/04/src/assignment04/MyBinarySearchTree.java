package assignment04;

import java.util.ArrayList;
import java.util.Comparator;


public class MyBinarySearchTree implements IBinarySearchTree {
    public int numOfComparisons = 0;

    /**
     * Root of the binary search tree.
     */
    protected BinaryTreeNode treeRoot;

    /**
     * Number of elements stored in the binary search tree.
     */
    protected int treeSize;

    /**
     * Initialization of the phone book based on a BST.
     */
    public MyBinarySearchTree() {
        treeRoot = null;
        treeSize = 0;
    }

    // This constructor is used for corrections - DO NOT CHANGE IT!
    public MyBinarySearchTree(BinaryTreeNode root, int size) {
        treeRoot = root;
        treeSize = size;
    }


    @Override
    public BinaryTreeNode getRoot() {
        return this.treeRoot;
    }

    @Override
    public void insert(int key, String elem) throws IllegalArgumentException {
        if (key < 0)
            throw new IllegalArgumentException("Key is < 0.");
        if (elem == null) throw new IllegalArgumentException();

        BinaryTreeNode newNode = new BinaryTreeNode(key, elem);
        if (!insert(treeRoot, newNode)) {
            treeRoot = newNode;
            treeSize++;
        }
    }

    private BinaryTreeNode findNode(int key) throws IllegalArgumentException {
        if (key < 0) {
            throw new IllegalArgumentException("Key is < 0.");
        }

        BinaryTreeNode n = treeRoot;

        while (n != null && n.key != key) {
            n = key < n.key ? n.left : n.right;
        }

        return n;
    }

    @Override
    public String find(int key) throws IllegalArgumentException {
        BinaryTreeNode n = findNode(key);

        return n != null ? n.elem : null;
    }

    private BinaryTreeNode findMinimumNode(BinaryTreeNode n) {
        while (n.left != null) {
            n = n.left;
        }

        return n;
    }

	// simple remove wrapper because I don't want to deal with decrementing treeSize all over the place
	@Override
	public boolean remove(int key) throws IllegalArgumentException {
		boolean success = _remove(key);

		if (success) {
			treeSize--;
		}

		return success;
	}

    private boolean _remove(int key) throws IllegalArgumentException {
        BinaryTreeNode n = findNode(key);

        if (n == null) {
            return false;
        }

        if (n.left == null && n.right == null) {
            // n has no children

            if (n == treeRoot) {
                treeRoot = null;
                return true;
            }

            if (n.parent.left == n) {
                n.parent.left = null;
            } else {
                n.parent.right = null;
            }
        } else if (n.left == null) {
            // n only has a child on the right

            if (n == treeRoot) {
                treeRoot = n.right;
                return true;
            }

            if (n.parent.left == n) {
                n.parent.left = n.right;
            } else {
                n.parent.right = n.right;
            }

            // do some parent-child relationship therapy
            n.right.parent = n.parent;
        } else if (n.right == null) {
            // n only has a child on the left

            if (n == treeRoot) {
                treeRoot = n.left;
                return true;
            }

            if (n.parent.left == n) {
                n.parent.left = n.left;
            } else {
                n.parent.right = n.left;
            }
        } else {
            // n has two children. the minimum value in the right subtree is the successor

            BinaryTreeNode minNode = findMinimumNode(n.right);

            // remove the successor from the tree
            _remove(minNode.key);
            // replace the item to be deleted with the successor
            n.elem = minNode.elem;
            n.key = minNode.key;
        }

        return true;
    }

    @Override
    public int size() {
        return treeSize;
    }

    private void recPostOrder(BinaryTreeNode node, ArrayList<BinaryTreeNode> arr) {
        if (node == null) {
            return;
        }

        recPostOrder(node.left, arr);
        recPostOrder(node.right, arr);

        arr.add(node);
    }

    private void recPreOrder(BinaryTreeNode node, ArrayList<BinaryTreeNode> arr) {
        if (node == null) {
            return;
        }

        arr.add(node);

        recPreOrder(node.left, arr);
        recPreOrder(node.right, arr);
    }

    private void recInOrder(BinaryTreeNode node, ArrayList<BinaryTreeNode> arr) {
        if (node == null) {
            return;
        }

        recInOrder(node.left, arr);

        arr.add(node);

        recInOrder(node.right, arr);
    }

    @Override
    public int[] toArrayPostOrder() {
        ArrayList<BinaryTreeNode> arr = new ArrayList<>();

        recPostOrder(treeRoot, arr);

        return arr.stream().mapToInt((n) -> n.key).toArray();
    }

    @Override
    public int[] toArrayPreOrder() {
        ArrayList<BinaryTreeNode> arr = new ArrayList<>();

        recPreOrder(treeRoot, arr);

        return arr.stream().mapToInt((n) -> n.key).toArray();
    }

    @Override
    public int[] toArrayInOrder() {
        ArrayList<BinaryTreeNode> arr = new ArrayList<>();

        recInOrder(treeRoot, arr);

        return arr.stream().mapToInt((n) -> n.key).toArray();
    }

    @Override
    public int getParent(int key) throws IllegalArgumentException {
        BinaryTreeNode n = findNode(key);

        if (n == null) {
            return -1;
        }

        if (n == treeRoot) {
            return n.key;
        }

        return n.parent.key;
    }

    @Override
    public boolean isRoot(int key) throws IllegalArgumentException {
        BinaryTreeNode n = findNode(key);

        // assuming that null should not be a root even when treeRoot is null
        return n != null && n == treeRoot;
    }

    @Override
    public boolean isInternal(int key) throws IllegalArgumentException {
        BinaryTreeNode n = findNode(key);

        if (n != null) {
            return n.left != null || n.right != null;
        } else {
            return false;
        }
    }

    @Override
    public boolean isExternal(int key) throws IllegalArgumentException {
        return !isInternal(key);
    }

    private int runtimeFindInTree(int key) {
        int c = 0;

        BinaryTreeNode n = treeRoot;

        while (n != null) {
            if (key == n.key) {
                return ++c;
            }

            if (key < n.key) {
                n = n.left;
            } else {
                n = n.right;
            }

            c += 2;
        }

        return c;
    }

    private int runtimeFindInList(ArrayList<Integer> arr, int key) {
        int c = 0;

        for (var item : arr) {
            if (item == key) {
                return ++c;
            }

            c++;
        }

        return c;
    }

    @Override
    public int[] runtimeComparison(ArrayList<Integer> list, int key) throws IllegalArgumentException {
        for (var item : list) {
            insert(item, String.valueOf(item));
        }

        return new int[]{ runtimeFindInTree(key), runtimeFindInList(list, key) };
    }

    public boolean isBST(IBinarySearchTree bst) throws IllegalArgumentException {
        if (bst == null) throw new IllegalArgumentException();

        BinaryTreeNode root = bst.getRoot();
        if (root == null) throw new IllegalArgumentException();

        if (root.left != null) {
            if (root.left.key > root.key) return false;
        }

        if (root.right != null) {
            if (root.right.key < root.key) return false;
        }

        return checkLeftSubTree(root.left, root) && checkRightSubTree(root.right, root);
    }

    public boolean checkLeftSubTree(BinaryTreeNode n, BinaryTreeNode root) {
        boolean left = true;
        boolean right = true;

        if (n == null) return true;

        if (n.left != null) {
            if (n.left.key <= n.key && n.left.key <= root.key) {
                left = checkLeftSubTree(n.left, root);
            } else return false;
        }

        if (n.right != null) {
            if (n.right.key > n.key && n.right.key <= root.key) {
                right = checkLeftSubTree(n.right, root);
            } else return false;
        }

        return left && right;
    }

    public boolean checkRightSubTree(BinaryTreeNode n, BinaryTreeNode root) {
        boolean left = true;
        boolean right = true;

        if (n == null) return true;

        if (n.left != null) {
            if (n.left.key <= n.key && n.left.key > root.key) {
                left = checkRightSubTree(n.left, root);
            } else return false;
        }

        if (n.right != null) {
            if (n.right.key > n.key && n.right.key > root.key) {
                right = checkRightSubTree(n.right, root);
            } else return false;
        }

        return left && right;
    }

    public String returnMinKey() {
        BinaryTreeNode n = treeRoot;

        while (n.left != null) {
            n = n.left;
        }

        return n.elem;
    }

    public int getDepth(int key) throws IllegalArgumentException {
        if (key < 0) {
            throw new IllegalArgumentException("Key is < 0.");
        }

        int depth = 0;
        BinaryTreeNode n = treeRoot;

        while (n != null && n.key != key) {
            depth++;
            n = key < n.key ? n.left : n.right;
        }

        return depth;
    }

    public boolean isTreeComplete() {
        return false;
    }

    //------------------------------------------------------------------------------------------
    //------------------------------------------------------------------------------------------
    //----- PRIVATE METHODS --------------------------------------------------------------------
    //------------------------------------------------------------------------------------------
    //------------------------------------------------------------------------------------------

    private boolean insert(BinaryTreeNode node, BinaryTreeNode x) {
        while (node != null) {
            int compare = node.key.compareTo(x.key);
            if (compare == 0) {
                return true;
            } else if (compare > 0) {
                if (node.left == null) {
                    node.left = x;
                    x.parent = node;
                    treeSize++;
                    return true;
                } else
                    node = node.left;
            } else {
                if (node.right == null) {
                    node.right = x;
                    x.parent = node;
                    treeSize++;
                    return true;
                } else
                    node = node.right;
            }
        }
        return false;
    }


}
