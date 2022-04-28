package assignment02.example01;

public class MyLinkedList implements IMyList {
	private MyListNode head;
	private MyListNode tail;
	private int size;

	/**
	 * Constructor.
	 * Initializes List.
	 */
	public MyLinkedList() {
		head = null;
		tail = null;
		size = 0;
	}
	
	public MyLinkedList(MyListNode newHead, MyListNode newTail, int newSize) {
		head = newHead;
		tail = newTail;
		size = newSize;
	}
	
	@Override
	public int getSize() {
		return size;
	}

	@Override
	public void insertSorted(int val) {
		size++;

		if (size == 1) {
			head = tail = new MyListNode(val);

			return;
		}

		MyListNode cur = head;
		MyListNode node = new MyListNode(val);

		do {
			if (val <= cur.getElement()) {
				node.setNext(cur);
				node.setPrev(cur.getPrev());

				cur.setPrev(node);

				if (node.getPrev() != null) {
					node.getPrev().setNext(node);
				} else {
					head = node;
				}

				if (node.getNext() == null) {
					tail = node;
				}

				return;
			}
		} while ((cur = cur.getNext()) != null);

		if (cur == null) {
			tail.setNext(node);
			node.setPrev(tail);
			node.setNext(null);

			tail = node;
		}
	}

	// Inserts a node at the end of a list
	private void insert(int val) {
		size++;

		MyListNode node = new MyListNode(val);

		if (size == 1) {
			head = tail = new MyListNode(val);

			return;
		}

		tail.setNext(node);
		node.setPrev(tail);
		node.setNext(null);

		tail = node;
	}

	@Override
	public int reorderList() {
		if (size == 0) {
			return -1;
		} else if (size == 1) {
			return (head.getElement() % 2 == 0) ? -1 : 0;
		}

		// ghetto algorithm

		int[] odd = new int[size];
		int oddLength = 0;

		int[] even = new int[size];
		int evenLength = 0;

		MyListNode cur = head;

		do {
			if (cur.getElement() % 2 == 0) {
				even[evenLength++] = cur.getElement();
			} else {
				odd[oddLength++] = cur.getElement();
			}
		} while ((cur = cur.getNext()) != null);

		clear();

		for (int i = 0; i < oddLength; i++) {
			insert(odd[i]);
		}

		for (int i = 0; i < evenLength; i++) {
			insert(even[i]);
		}

		return evenLength == 0 ? -1 : oddLength;
	}

	@Override
	public void clear() {
		head = tail = null;

		size = 0;
	}
	
	@Override
	public int get(int index) throws IllegalArgumentException {
		if (index > (size - 1) || index < 0) {
			throw new IllegalArgumentException("Index out of bounds");
		}

		int i = 0;
		MyListNode cur = head;

		do {
			if (i == index) {
				return cur.getElement();
			}

			i++;
		} while ((cur = cur.getNext()) != null);

		throw new RuntimeException("Logic error");
	}
	
	@Override
	public boolean remove(int val) {
		if (size == 0) {
			return false;
		}

		MyListNode cur = head;

		do {
			if (cur.getElement() == val) {
				MyListNode prev = cur.getPrev();
				MyListNode next = cur.getNext();

				if (prev != null) {
					prev.setNext(next);
				}

				if (next != null) {
					next.setPrev(prev);
				}

				if (cur == tail) {
					tail = prev;
				}

				if (cur == head) {
					head = next;
				}

				size--;

				return true;
			}
		} while ((cur = cur.getNext()) != null);

		return false;
	}
	
	@Override
	public void removeDuplicates() {
		if (size <= 1) {
			return;
		}

		// iterate from the end because remove() iterates from beginning
		for (int i = size - 1; i >= 0; i--) {
			int value = get(i);

			for (int j = 0; j < i; j++) {
				if (value == get(j)) {
					remove(value);
				}
			}
		}
	}

	public String toString() {
		if (size == 0) {
			return "empty list";
		}

		StringBuilder str = new StringBuilder();

		MyListNode cur = head;

		do {
			str.append(cur.getElement());
			str.append(", ");
		} while ((cur = cur.getNext()) != null);

		return str.toString();
	}

	/***********************************************************
	 * DON'T TOUCH THIS CODE
	 * Methods for testing your code after submission.
	***********************************************************/
	public MyListNode getHead() { return head; }
	public MyListNode getTail() { return tail; }
}
