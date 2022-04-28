package assignment02.example01;


public class MyListNode {

	private int element;
	private MyListNode next, prev;
	
	public MyListNode() {
		this.element = 0;
		this.next = null;
		this.prev = null;
	}
	
	public MyListNode(int element) {
		this.element = element;
		this.next = null;
		this.prev = null;
	}
	
	public int getElement() 				{ return this.element; }
	public void setElement(int element)		{ this.element = element; }
	public MyListNode getNext() 			{ return this.next; }
	public MyListNode getPrev() 			{ return this.prev; }
	public void setNext(MyListNode next)	{ this.next = next; }
	public void setPrev(MyListNode prev)	{ this.prev = prev; }
}

