package assignment05;

import java.util.NoSuchElementException;

public interface IMyPriorityQueue {
	
	/**
	 * @return True if the PQ is empty, false otherwise.
	 */
	public boolean isEmpty();	
	
	/**

	 * @return the current size of the PQ.
	 */
	public int size();
	
	/**
	 * This method inserts a new element into the PQ. Make sure that every time the heap array size n is exceeded,
	 * i.e., when the n+1th element shall be inserted, the array size has to be doubled.
	 * 
	 * @param elem to be inserted into the PQ.
	 */
	public void insert(int elem);
	
	/**
	 * This method removes and returns the min element from the PQ.
	 * 
	 * @return the min element of the PQ.
	 * @throws NoSuchElementException if the PQ is empty.
	 */
	public int removeMin() throws NoSuchElementException;
	
	/**
	 * This method returns the min element from the PQ without removing it.
	 * @return the min element of the PQ or throw a NoSuchElementException if the PQ is empty.
	 * @throws NoSuchElementException if the PQ is empty.
	 */
	public int min() throws NoSuchElementException;
}
