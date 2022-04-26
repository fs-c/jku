package assignment02.example02.skeleton;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;

public class MySingleLinkedListTest {
	@Test
	/**
	 *  This unit test case shall do the list benachmark by executing compareLists() with various values (1000, ...).
	 */
	public void testCompareLists() {
		 int[] sizes = { 1000, 10000, 100000, 200000, 300000 };

		 for (int size : sizes) {
			 compareLists(size);
		 }
	}

    /**
	 * This method compares the prepend-performance of a Single Linked List with the ArrayList from the Java standard library.
	 * It measures the time needed for inserting num number of elements into a single linked list, as well as for the ArrayList.
	 * To get more meaningful results the measurement is done 3x and the average is calculated - for each list type.
	 * The result is printed in the terminal/console.
	 * 
	 * Possible example output for compareLists(10000) could be:
	 *        "10.000 elements:  LinkedList: 19231ns; StdList: 41105ns; --> LinkedList is 21874ns faster!"
	 *
	 * @param num
	 *     The number of elements that shall be inserted at the beginning of the list (=prepend)
	 *     
	 * @throws IllegalArgumentException
	 *     if num is less than 0.
	 */
	private void compareLists(int num) throws IllegalArgumentException {
		if (num < 0) {
			throw new IllegalArgumentException("Number of elements must be at least zero");
		}

		long linkedListResult = benchmarkFunction(() -> {
			MySingleLinkedList list = new MySingleLinkedList();

			for (int i = 0; i < num; i++) {
				list.prepend(i);
			}
		});

		long arrayListResult = benchmarkFunction(() -> {
			ArrayList<Integer> list = new ArrayList<>();

			for (int i = 0; i < num; i++) {
				list.add(0, i);
			}
		});

		System.out.format("[%d elements] linked list: %dns (100%%), array list: %dns (%d%%)\n",
				num, linkedListResult, arrayListResult, (arrayListResult / linkedListResult) * 100);
	}

	private long benchmarkFunction(Runnable func) {
		long[] times = new long[3];

		for (int i = 0; i < 3; i++) {
			long before = System.nanoTime();

			func.run();

			long after = System.nanoTime();

			times[i] = after - before;
		}

		return (times[0] + times[1] + times[2]) / 3;
	}
}

