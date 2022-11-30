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
		for (ChainingHashNode node : table) {
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
		return this.hashTable;
	}

	@Override
	public int size() {
		return size;
	}

	@Override
	public boolean insert(int key) {
		int hash = getHashCode(key);

		if (hashTable[hash] == null) {
			hashTable[hash] = new ChainingHashNode(key);
		} else {
			var node = hashTable[hash];

			if (node.next == null && node.key == key) {
				return false;
			}

			while (node.next != null) {
				if (node.key == key) {
					return false;
				}

				node = node.next;
			}

			node.next = new ChainingHashNode(key);
		}

		size++;

		return true;
	}

	@Override
	public boolean contains(int key) {
		int hash = getHashCode(key);

		if (hashTable[hash] != null) {
			var node = hashTable[hash];
			do {
				if (node.key == key) {
					return true;
				}

				node = node.next;
			} while (node != null);
		}

		return false;
	}

	@Override
	public boolean remove(int key) {
		int hash = getHashCode(key);

		if (hashTable[hash] != null) {
			var node = hashTable[hash];

			if (node.key == key) {
				hashTable[hash] = node.next;
				size--;
				return true;
			}

			while (node.next != null) {
				if (node.next.key == key) {
					node.next = node.next.next;
					size--;
					return true;
				}

				node = node.next;
			}
		}

		return false;
	}

	@Override
	public void clear() {
		for (int i = 0; i < capacity; i++) {
			hashTable[i] = null;
		}

		size = 0;
	}

	@Override
	public String toString() {
		var sb = new StringBuilder();

		for (int i = 0; i < capacity; i++) {
			sb.append(i).append(" {");

			var node = hashTable[i];
			while (node != null) {
				sb.append(node.key);

				if (node.next != null) {
					sb.append(", ");
				}

				node = node.next;
			}

			sb.append("}");

			if (i < capacity - 1) {
				sb.append(", ");
			}
		}

		return sb.toString();
	}
}
