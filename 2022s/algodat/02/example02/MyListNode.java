package assignment02.example02.skeleton;


public class MyListNode {

	private int element;
	private MyListNode next;
	
	public MyListNode() {
		this.next = null;
	}
	
	public MyListNode(int element) {
		this.element = element;
		this.next = null;
	}
	
	public int getElement() 				{ return this.element; }
	public void setElement(int element)		{ this.element = element; }
	public MyListNode getNext() 			{ return this.next; }
	public void setNext(MyListNode next)	{ this.next = next; }
}

