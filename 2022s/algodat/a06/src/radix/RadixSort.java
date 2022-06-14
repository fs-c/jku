package radix;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

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

    // gets the amount of digits of the given number
    private static int getDigits(int val) {
        return (int)Math.floor(Math.log10(val)) + 1;
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
    public static ArrayList<Integer> sort(int[] list) throws IllegalArgumentException {
        // As this method is static, we need to clear the snapshots before each sort
        bucketlistSnapshots.clear();

        if (list == null) {
            throw new IllegalArgumentException("list is null");
        }

        ArrayList<Integer> sortedList = new ArrayList<Integer>(list.length);
        for (int k : list) {
            sortedList.add(k);
        }

        // get maximum amount of digits to know when to stop
        int maxDigits = 0;
        for (int val : list) {
            maxDigits = Math.max(maxDigits, getDigits(val));
        }

        for (int i = 0; i < maxDigits; i++) {
            // initialize bucket list
            ArrayList<ArrayList<Integer>> buckets = new ArrayList<>(radix);
            for (int j = 0; j < radix; j++) {
                buckets.add(new ArrayList<>());
            }

            // distribute elements to buckets
            for (int val : sortedList) {
                int digit = getDigit(val, i);

                if (digit >= radix) {
                    throw new IllegalArgumentException("digit is greater than radix");
                }

                buckets.get(digit).add(val);
            }

            addBucketlistSnapshot(buckets);

            // commit buckets to list
            int j = 0;
            for (ArrayList<Integer> bucket : buckets) {
                for (int val : bucket) {
                    sortedList.set(j, val);
                    j++;
                }
            }
        }

        // :)
        Collections.reverse(sortedList);

        return sortedList;
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