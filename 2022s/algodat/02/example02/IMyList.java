package assignment02.example02.skeleton;

/*********************************************************
 * Interface for EXAMPLE 2
 * This class is used for example 2 only.
 *********************************************************/
public interface IMyList {
	MyListNode getHead();			// Returns the head of your list
	MyListNode getTail();			// Returns the tail of your list
	
	/**
	 * Inserts an element at the beginning of the list.
	 *
	 * @param val to be inserted
	 */
	void prepend (int val);
}
