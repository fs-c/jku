package assignment05;

import java.util.NoSuchElementException;

public class MinHeap implements IMyPriorityQueue {
	/********************************************************
	 * REQUIRED FOR UNITTESTS! DO NOT REMOVE THIS METHOD
 	 ********************************************************/
	private int[] heap; // int-array that represents your heap
	public int[] getHeap() { return heap; }
	/********************************************************/

	private int size = 0; // number of elements in the heap

	// Constructor that initially defines the allocated memory for the heap.
	public MinHeap(int initCapacity) {
		heap = new int[initCapacity];
	}

	private void swap(int i, int j) {
		int tmp = heap[i];
		heap[i] = heap[j];
		heap[j] = tmp;
	}

	private void filterUp(int index) {
		int parent = (index - 1) / 2;

		// while we're not at the top and the heap is not in order
		while (index > 0 && heap[parent] > heap[index]) {
			// fix this level of the heap
			swap(parent, index);

			// move up
			index = parent;
			parent = (index - 1) / 2;
		}
	}

	private void filterDown(int index) {
		// get children
		int left = 2 * index + 1;
		int right = 2 * index + 2;

		// get smallest child

		int smallest = index;

		if (left < size && heap[left] < heap[index]) {
			smallest = left;
		}

		if (right < size && heap[right] < heap[smallest]) {
			smallest = right;
		}

		// if we're not already the smallest, filter downwards
		if (smallest != index) {
			swap(index, smallest);
			filterDown(smallest);
		}
	}

    @Override
	public void insert(int val) {
		if (size == heap.length) {
			// double the size of the heap
			int[] newHeap = new int[heap.length * 2];
			System.arraycopy(heap, 0, newHeap, 0, heap.length);
			heap = newHeap;
		}

		// insert val into the farthest possible position and increase the size
		heap[size++] = val;

		// filter up the new element
		filterUp(size - 1);
	}

    @Override
	public boolean isEmpty() {
		return size() == 0;
	}

    @Override
	public int min() throws NoSuchElementException {
		if (size == 0) {
			throw new NoSuchElementException();
		}

		return heap[0];
	}

    @Override
	public int removeMin() throws NoSuchElementException {
		int oldMin = min(); // this will also throw our exception if the heap is empty

		// replace min node with the lowest and rightmost node
		heap[0] = heap[--size];

		// filter down the new root
		filterDown(0);

		return oldMin;
	}

    @Override
	public int size() {
		return size;
	}
}
