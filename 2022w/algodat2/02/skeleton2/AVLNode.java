package assignment02;

public class AVLNode {
	public AVLNode parent = null;
	public AVLNode left = null;
	public AVLNode right = null;

	public int key;
	public float value;

	public int height = 0; // To determine node height in O(1)

	public AVLNode(int key, float value) {
		this.key = key;
		this.value = value;
	}

	@Override
	public String toString() {
		return "key:" + key + ", value: " + value;
	}
}


