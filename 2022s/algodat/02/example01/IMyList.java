package assignment02.example01;

/*********************************************************
 * Interface for EXAMPLE 1
 * This class is used for example 1 only.
 *********************************************************/

public interface IMyList {
	/**
	 * Returns number of elements in the List (in O(1))
	 */
	int getSize();

	/**
	 * Adds the element val to the list (sorted in ascending order). In case of duplicates
	 * the new element is inserted either before or after the existing duplicate.
	 *
	 * @param val to be inserted into the list.
	 */
	void insertSorted(int val);
	
	/**
	 * Clears the list (in O(1))
	 */
	void clear();				
	
	/**
	 *  Returns the element at specific list position (no removal). First list element has index position 0.
	 * 	If the index position is out of range an IllegalArgumentException is thrown.
	 *
	 * @param index position in the list
	 * @return the value of the element at the given index position
	 * @throws IllegalArgumentException if the given index position is out of range.
	 */
	int get(int index) throws IllegalArgumentException;
	
	/**
	 * Removes first occurrence of element val (starting from head) and returns true if this was successful.
	 * In error case (e.g. if the given element is not found) return false.
	 *
	 * @param val to be removed
	 * @return true if element was found and removed, false otherwise.
	 */
	boolean remove(int val);

	/**
	 * Removes all duplicates from the list.
	 */
	void removeDuplicates();
	
	/**
	 * Reorders the list so that at the beginning there are all odd values, then followed by all
	 * even values, e.g. [1,4,6,7] -> [1,7,4,6]. The position (starting with index 0) of the first
	 * element with an even value is returned. In case there are only odd values return -1.
	 * Ascending order within the sequences of odd and even values must be retained.
	 *
	 * @return the index position of the first element with an even value.
	 */
	int reorderList();
	
	MyListNode getHead();			//Returns the head of your list
	MyListNode getTail();			//Returns the tail of your list
}
