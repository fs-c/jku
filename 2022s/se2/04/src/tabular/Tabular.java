package tabular;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;

public interface Tabular extends Iterable<Integer> {

    /* TODO abstract methods of interface Tabular */

    /* TODO default methods of interface Tabular */

    int rowCount();
    int colCount();

    String rowName(int row);
    String colName(int col);

    Iterable<Integer> iterableRow(int row);
    Iterable<Integer> iterableCol(int col);

    default int[] rowSums() {
        int[] sums = new int[rowCount()];

        for (int rowIdx = 0; rowIdx < rowCount(); rowIdx++) {
            int sum = 0;

            for (final int value : iterableRow(rowIdx)) {
                sum += value;
            }

            sums[rowIdx] = sum;
        }

        return sums;
    }

    default int[] colSums() {
        int[] sums = new int[colCount()];

        for (int colIdx = 0; colIdx < colCount(); colIdx++) {
            int sum = 0;

            for (final int value : iterableCol(colIdx)) {
                sum += value;
            }

            sums[colIdx] = sum;
        }

        return sums;
    }

    default double[] rowAverages() {
        int[] sums = rowSums();

        return Arrays.stream(sums).asDoubleStream().map((x) -> x / colCount())
                .toArray();
    }

    default double[] colAverages() {
        int[] sums = colSums();

        return Arrays.stream(sums).asDoubleStream().map((x) -> x / rowCount())
                .toArray();
    }

    default int sum() {
        return Arrays.stream(rowSums()).sum() + Arrays.stream(colSums()).sum();
    }

    default double average() {
        return Arrays.stream(colAverages()).sum() / colCount();
    }

    @Override
    default Iterator<Integer> iterator() {
        return new Iterator<>() {
            int rowIndex = 0;
            Iterator<Integer> rowIterator = iterableRow(0).iterator();

            @Override
            public boolean hasNext() {
                return rowIterator.hasNext() || rowIndex < rowCount() - 1;
            }

            @Override
            public Integer next() {
                if (!rowIterator.hasNext()) {
                    rowIndex++;
                    rowIterator = iterableRow(rowIndex).iterator();
                }
                return rowIterator.next();
            }
        };
    }
}
