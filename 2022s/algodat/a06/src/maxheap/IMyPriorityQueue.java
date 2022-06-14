package maxheap;

import java.util.NoSuchElementException;
public interface IMyPriorityQueue {
	// For testing purpose only.
	public int[] getHeap();
			
	/**
	 * 
	 * @return the current size of the PQ.
	 */
	public int size();
	
	/**
	 * This method removes and returns the max element from the PQ. 
	 * 
	 * @return the max element of the PQ.
	 * @throws NoSuchElementException if the PQ is empty.
	 */
	public int removeMax() throws NoSuchElementException;
	
	/**
	 * Checks if the element val is already stored.
	 * 
	 * @param val is the key to be searched
	 * @return true if val is found, false otherwise or if heap is empty.
	 */
	public boolean contains(int val);
}
