package maxheap;

import java.util.NoSuchElementException;

public class MaxHeap implements IMyPriorityQueue {
	private int[] heap;
	private int size;
	
	// REQUIRED FOR UNIT TESTING! DO NOT REMOVE THIS METHOD
	public int[] getHeap() {
		return heap;
	}
	
    /**
     * Use this constructor to create the MaxHeap bottom-up and in-place.
     * @throws IllegalArgumentException if list is null;
     */
    public MaxHeap(int[] list) throws IllegalArgumentException {
		if (list == null) {
			throw new IllegalArgumentException("list is null");
		}

		heap = list;
		size = list.length;

		constructBottomUp();
	}

	private void constructBottomUp() {
		for (int i = size / 2; i >= 0; i--) {
			boolean isHeap = false;

			int j = i;		 // inner loop index
			int e = heap[i]; // the element to be put in place

			// while we're not done and still have children
			while (!isHeap && leftChild(j) < size) {
				int c = leftChild(j); // the element to be compared with e

				// if c has a sibling on the right and that one is bigger...
				if ((c + 1) < size && heap[c] < heap[c + 1]) {
					// ...work with the bigger one
					c++;
				}

				if (heap[c] < e) {
					// if e is bigger than c (one of its descendants) we're done
					isHeap = true;
				} else {
					// otherwise, swap c and j and continue
					heap[j] = heap[c];
					j = c;
				}
			}

			heap[j] = e;
		}
	}

	private int parent(int i) {
		return (i - 1) / 2;
	}

	private int leftChild(int i) {
		return 2 * i + 1;
	}

	private int rightChild(int i) {
		return 2 * i + 2;
	}

	private void swap(int i, int j) {
		int temp = heap[i];
		heap[i] = heap[j];
		heap[j] = temp;
	}

	private void downHeap(int i) {
		int left = leftChild(i);
		int right = rightChild(i);

		int largest = i;

		if (left < size && heap[left] > heap[largest]) {
			largest = left;
		}

		if (right < size && heap[right] > heap[largest]) {
			largest = right;
		}

		// continue down if we are not the largest
		if (largest != i) {
			swap(i, largest);
			downHeap(largest);
		}
	}

    public int size() {
		return this.size;
	}
    
    /**
	 * This method removes and returns the max element from the PQ. 
	 * 
	 * @return the max element of the PQ.
	 * @throws NoSuchElementException if the PQ is empty.
	 */
    @Override
	public int removeMax() throws NoSuchElementException {
		if (size == 0) {
			throw new NoSuchElementException("PQ is empty");
		}

		int max = heap[0];

		heap[0] = heap[--size];
		downHeap(0);

		return max;
	}

	private boolean recursiveContains(int i, int val) {
		if (i >= size || heap[i] < val) {
			// we went too far
			return false;
		} else if (heap[i] == val) {
			return true;
		} else {
			return recursiveContains(leftChild(i), val) || recursiveContains(rightChild(i), val);
		}
	}
	
    /**
	 * Checks if the element val is already stored.
	 * 
	 * @param val is the key to be searched
	 * @return true if val is found, false otherwise (or if heap is empty).
	 */
    @Override
	public boolean contains(int val) {
		if (size == 0) {
			return false;
		}

		return recursiveContains(0, val);
	}

    /**
	 * This method sorts the given int[] list in-place using the constructor MaxHeap(int[] list).
	 * 
	 * @param list contains the elements to be sorted in-place.
	 * @throws IllegalArgumentException if list is null.
	 */
	public static void sort(int[] list) throws IllegalArgumentException {
		if (list == null) {
			throw new IllegalArgumentException("list is null");
		}

		var heap = new MaxHeap(list);

		for (int i = heap.size(); i > 0; i--) {
			list[i - 1] = heap.removeMax();
		}
	}
}
