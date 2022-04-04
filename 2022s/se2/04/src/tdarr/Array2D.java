package tdarr;

import tabular.Tabular;

import java.util.Iterator;

public class Array2D implements Tabular {
    private final int[][] data;

    public Array2D(int rows, int cols) {
        this.data = new int[rows][cols];
    }

    public void set(int row, int col, int val) {
        if (row >= 0 && row < data.length && col >= 0 && col < data[0].length) {
            data[row][col] = val;
        } else {
            throw new IndexOutOfBoundsException("Row " + row + " and col " + col + " out of bounds");
        }
    }

    public int get(int row, int col) {
        if (row >= 0 && row < data.length && col >= 0 && col < data[0].length) {
            return data[row][col];
        } else {
            throw new IndexOutOfBoundsException("Row " + row + " and col " + col + " out of bounds");
        }
    }

    @Override
    public int rowCount() {
        return data.length;
    }

    @Override
    public int colCount() {
        return data[0].length;
    }

    @Override
    public String rowName(int row) {
        return "Row " + row;
    }

    @Override
    public String colName(int col) {
        return "Column " + col;
    }

    @Override
    public Iterable<Integer> iterableRow(int row) {
        return () -> new Iterator<>() {
            int colIndex = 0;

            @Override
            public boolean hasNext() {
                return colIndex < data.length;
            }

            @Override
            public Integer next() {
                return data[row][colIndex++];
            }
        };
    }

    @Override
    public Iterable<Integer> iterableCol(int col) {
        return () -> new Iterator<>() {
            int rowIndex = 0;

            @Override
            public boolean hasNext() {
                return rowIndex < data[rowIndex].length;
            }

            @Override
            public Integer next() {
                return data[rowIndex++][col];
            }
        };
    }

    /* TODO implement Tabular */
}
