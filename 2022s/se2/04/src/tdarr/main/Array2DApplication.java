package tdarr.main;

import inout.Out;
import tdarr.Array2D;

public class Array2DApplication {

    public static void main(String[] args) {
        Array2D arr = new Array2D(10, 6);

        addExampleData(arr);

        Out.println();
        Out.println("-----------------------------------------------");
        Out.println("TwoDimensionalArrayApplication: ");
        Out.println("-----------------------------------------------");

        int[] rowSums = arr.rowSums();
        for (int i = 0; i < rowSums.length; i++) {
            Out.println(String.format("Average of %s: %d", arr.rowName(i), rowSums[i]));
        }
        Out.println();

        double[] colAverages = arr.colAverages();
        for (int i = 0; i < colAverages.length; i++) {
            Out.println(String.format("Average of %s: %4.1f", arr.colName(i), colAverages[i]));
        }
        Out.println();

        Out.println(String.format("Average cell: %4.1f", arr.average()));
    }

    private static void addExampleData(Array2D arr) {
        arr.set(0, 0, 8);
        arr.set(0, 1, 9);
        arr.set(0, 2, 7);
        arr.set(0, 3, 10);
        arr.set(0, 4, 7);
        arr.set(0, 5, 9);
        arr.set(1, 0, 4);
        arr.set(1, 1, 0);
        arr.set(1, 2, 6);
        arr.set(1, 3, 6);
        arr.set(1, 4, 2);
        arr.set(1, 5, 4);
        arr.set(2, 0, 9);
        arr.set(2, 1, 5);
        arr.set(2, 2, 6);
        arr.set(2, 3, 7);
        arr.set(2, 4, 8);
        arr.set(2, 5, 8);
        arr.set(3, 0, 5);
        arr.set(3, 1, 6);
        arr.set(3, 2, 7);
        arr.set(3, 3, 0);
        arr.set(3, 4, 8);
        arr.set(3, 5, 8);
        arr.set(4, 0, 7);
        arr.set(4, 1, 8);
        arr.set(4, 2, 5);
        arr.set(4, 3, 6);
        arr.set(4, 4, 3);
        arr.set(4, 5, 9);
        arr.set(5, 0, 7);
        arr.set(5, 1, 6);
        arr.set(5, 2, 8);
        arr.set(5, 3, 9);
        arr.set(5, 4, 10);
        arr.set(5, 5, 9);
        arr.set(6, 0, 5);
        arr.set(6, 1, 1);
        arr.set(6, 2, 4);
        arr.set(6, 3, 5);
        arr.set(6, 4, 7);
        arr.set(6, 5, 6);
        arr.set(7, 0, 10);
        arr.set(7, 1, 10);
        arr.set(7, 2, 10);
        arr.set(7, 3, 10);
        arr.set(7, 4, 9);
        arr.set(7, 5, 10);
        arr.set(8, 0, 8);
        arr.set(8, 1, 9);
        arr.set(8, 2, 7);
        arr.set(8, 3, 10);
        arr.set(8, 4, 7);
        arr.set(8, 5, 9);
        arr.set(9, 0, 3);
        arr.set(9, 1, 3);
        arr.set(9, 2, 4);
        arr.set(9, 3, 2);
        arr.set(9, 4, 9);
        arr.set(9, 5, 10);
    }

}
