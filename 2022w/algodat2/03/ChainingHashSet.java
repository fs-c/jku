public class ChainingHashSet implements IHashSet {

	private ChainingHashNode hashTable[];
	private int size = 0;
	private int capacity = 0;

	/**
	 * Constructor with hash table initialization
	 */
	public ChainingHashSet(int capacity) {
		hashTable = new ChainingHashNode[capacity];
		this.capacity = capacity;
		this.size = 0;
	}

	@Override
	public void setHashTable(ChainingHashNode[] table) {
		this.hashTable = table;
		this.capacity = table.length;
		this.size = 0;
		for(ChainingHashNode node : table) {
			while(node != null) {
				this.size++;
				node = node.next;
			}
		}
	}

	@Override
	public int getHashCode(int key) {
		return key % capacity;
	}

	@Override
	public ChainingHashNode[] getHashTable() {
		// ...
		return null;
	}

	@Override
	public int size() {
		// ...
		return -1;
	}

	@Override
	public boolean insert(int key) {
		// ...
		return false;
	}

	@Override
	public boolean contains(int key) {
		// ...
		return false;
	}

	@Override
	public boolean remove(int key) {
		// ...
		return false;
	}

	@Override
	public void clear() {
		// ...
	}

	@Override
	public String toString() {
		// ...
		return "";
	}
}
