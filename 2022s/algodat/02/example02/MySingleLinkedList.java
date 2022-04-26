package assignment02.example02.skeleton;


public class MySingleLinkedList implements IMyList {

	private MyListNode head;
	private MyListNode tail;

	
	/**
	 * Constructors.
	 * Initializes List.
	 */
	public MySingleLinkedList() {
		head = null;
		tail = null;
	}
	
	/* DO NOT CHANGE THIS SPECIAL CONSTRUCTOR */
	public MySingleLinkedList(MyListNode newHead, MyListNode newTail) {
		head = newHead;
		tail = newTail;
	}
	
   	public MyListNode getHead() { return head; }
	public MyListNode getTail() { return tail; }
	
	
	@Override
	public void prepend(int val) {
		MyListNode node = new MyListNode(val);

        if (head == null && tail == null) {
			head = tail = node;

			return;
		}

		node.setNext(head);
		head = node;
	}

}
