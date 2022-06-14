package radix;

import java.util.ArrayList;

public class RadixSort {
	static int radix = 7;
	
	/**
	 * This variable contains snapshots of the bucketlist that shall be taken at the end of each distribution
	 * phase (= each time after all elements to be sorted have been assigned to a bucket).
	 *
	 *                 -------------------- List containing the bucketlist snapshots
	 *                 |       ------------ List of buckets
	 *                 |       |         -- Content of a bucket
	 *                 |       |         |                                                                */
    private static ArrayList<ArrayList<ArrayList<Integer>>> bucketlistSnapshots = new ArrayList<>();
    
    /**
     * This method returns the bucketlist snapshots.
     * 
     * @return bucketlistSnapthos
     */
	public static ArrayList<ArrayList<ArrayList<Integer>>> getBucketlistSnapshots(){
		return bucketlistSnapshots;
	}

	// gets the digit at the given position of the given number
	private static int getDigit(int val, int pos) {
		return (val / (int)Math.pow(10, pos)) % 10;
	}

	/**
	 * Sort a given array using the RadixSort algorithm. After each distribution phase (when all elements have been
	 * assigned to buckets) a bucketlist snapshot must be made by calling the provided method addBucketlistSnapshot().
	 *
	 * As this method is static the bucketlistSnapshots-container must be cleared before each call.
	 * @param list contains the elements to be sorted.
	 * @return the sorted list
     * @throws IllegalArgumentException if list is null.
	 */
	public static ArrayList<Integer> sort(int[] list) throws IllegalArgumentException{
		// As this method is static, we need to clear the snapshots before each sort
		bucketlistSnapshots.clear();

		if (list == null){
			throw new IllegalArgumentException("list is null");
		}

		ArrayList<ArrayList<Integer>> buckets = new ArrayList<>(radix);

		for (int val : list) {
			int digit = getDigit(val, 0);

			buckets.get(digit).add(val);
		}
	}
	
	
	//---------------------------------------------------------------------------------------------------------

	/**
	 * This method creates a snapshot (clone) of the bucketlist and adds it to the bucketlistSnapshots.
	 * You shall call this method AFTER each distribution phase of the sorting procedure just BEFORE
	 * the merge step (collection phase).
	 *
	 * This method is not part of the algorithm itself, it's just required for detailed unit testing of your
	 * implementation.
	 *
	 * @param bucketlist is your current bucketlist, after assigning all elements to be sorted to the buckets.
	 */
	private static void addBucketlistSnapshot(ArrayList<ArrayList<Integer>> bucketlist) {
		// clone list!
		ArrayList<ArrayList<Integer>> lstClone = new ArrayList<>();
		
		for(int i = 0; i<bucketlist.size(); i++) {
			lstClone.add(new ArrayList<Integer>());
			lstClone.get(i).addAll(bucketlist.get(i));
		}
		
		// add clone to the bucketlistSnapshots
		bucketlistSnapshots.add(lstClone);
	}
}