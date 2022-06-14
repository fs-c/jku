package four.game;

import inout.Out;

/**
 * The ConnectFour board that tracks the {@link #field} states.
 */
public class Board {
    private static final int MAX_DIM = 9;

    private final int rows;
    private final int cols;

    private final Stone[][] field;

    // TODO: document this constructor with all parameters and thrown exceptions;
    //  link to #MAX_DIM to describe the exception and Stone#None to describe the initial field state

    /**
     * Creates a new and empty (filled with {@linkplain Stone#None}) board with the given dimensions.
     *
     * @param rows the number of rows the board should have
     * @param cols the number of columns the board should have
     * @throws IllegalArgumentException if the dimensions are invalid (less than 0 or greater than {@link #MAX_DIM})
     */
    public Board(int rows, int cols) {
        // TODO: verify that arguments are GREATER 0 and NOT LARGER than MAX_DIM

        if (rows <= 0 || cols <= 0 || rows > MAX_DIM || cols > MAX_DIM) {
            throw new IllegalArgumentException("Invalid board dimensions");
        }

        this.rows = rows;
        this.cols = cols;
        this.field = new Stone[rows][cols];
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                field[r][c] = Stone.None;
            }
        }
    }

    /**
     * {@linkplain Out#println Prints} the board to the console.
     */
    public void print() {
        Out.println("|----------------------|");
        Out.print("|");


        for (int c = 1; c <= cols; c++) {
            Out.print(" " + c + " ");
        }
        Out.println(" |");
        Out.println("|----------------------|");
        for (int r = 0; r < rows; r++) {
            Out.print("|");
            for (int c = 0; c < cols; c++) {
                Out.print(getStone(r, c).outputString());
            }
            Out.println(" | ");
        }
        Out.println("|----------------------|");
    }

    // TODO: document

    /**
     * Gets the stone on a given cell.
     * @param row the row number of the cell
     * @param col the column number of the cell
     * @throws IllegalArgumentException if the cell is invalid (see {@link #isValidCell})
     * @return the stone on the cell
     */
    public Stone getStone(int row, int col) {
        if (!isValidCell(row, col)) {
            throw new IllegalArgumentException("Invalid cell at row " + row + ", col " + col);
        }

        if (row < 0 || row >= rows || col < 0 || col >= cols) {
            return Stone.None;
        }
        return field[row][col];
    }

    // TODO: document and link to getNextFreeRow in documentation

    /**
     * "Drops" a stone into a given column.
     * @param col the column number to drop the stone into
     * @param stone the stone to drop
     * @return the row that the stone ended up in
     * @throws IllegalArgumentException if stone is invalid ({@link Stone#None}) or if the move is invalid (see {@link #isValidMove})
     */
    public int setStone(int col, Stone stone) {
        if (stone == Stone.None || !isValidMove(col)) {
            throw new IllegalArgumentException("Illegal move!");
        }
        int row = getNextFreeRow(col);
        assert row >= 0 && row < rows;
        field[row][col] = stone;
        return row;
    }

    // TODO: document

    /**
     * Checks whether the given cell position is valid. A cell is valid if its coordinates are within the board's dimensions.
     * @param row the row number of the cell
     * @param col the column number of the cell
     * @return whether the cell position is valid
     */
    public boolean isValidCell(int row, int col) {
        return row >= 0 && row < rows && col >= 0 && col < cols;
    }

    /**
     * Checks if a move is valid.
     * <br/>
     * A move is valid if the column number is valid and has space for at least one stone.
     *
     * @param col the column to check
     * @return {@code true} if the given column is valid; {@code false otherwise}
     */
    public boolean isValidMove(int col) {
        // TODO: implement based on tests and documentation

        return (col >= 0 && col < cols && getNextFreeRow(col) != -1);
    }

    /**
     * Determines the lowest {@linkplain #isEmpty(int, int) empty} row for the given column number.
     *
     * @param col the column number
     * @return the next free row or -1 if the column is full
     * @throws IllegalArgumentException if the given column is invalid
     */
    public int getNextFreeRow(int col) {
        // TODO: implement method based on documentation

        if (!isValidCell(0, col)) {
            throw new IllegalArgumentException("Invalid column number");
        }

        for (int r = rows - 1; r >= 0; r--) {
            if (getStone(r, col) == Stone.None) {
                return r;
            }
        }

        return -1;
    }

    /**
     * Checks if a cell is empty, i.e., it contains {@linkplain Stone#None no stone}.
     *
     * @param row the row number of the cell
     * @param col the column number of the cell
     * @return {@code true} if the given cell is empty; {@code false} otherwise
     */
    public boolean isEmpty(int row, int col) {
        return getStone(row, col) == Stone.None;
    }

    /**
     * Checks if the board is full.
     *
     * @return {@code true}, if every cell contains a {@link Stone}; {@code false} otherwise.
     */
    public boolean isFull() {
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                if (getStone(r, c) == Stone.None) {
                    return false;
                }
            }
        }
        return true;
    }

    // TODO: document and use @code-Tags for true and false

    /**
     * Checks if the given stone has four connected stones in any direction.
     * @param row the row number of the stone
     * @param col the column number of the stone
     * @return {@code true} if the given stone has four connected; {@code false} otherwise
     */
    public boolean hasFourConnected(int row, int col) {
        return countHorizontally(row, col) >= 4 ||
                countVertically(row, col) >= 4 ||
                countDiagonallyLeft(row, col) >= 4 ||
                countDiagonallyRight(row, col) >= 4;
    }

    /**
     * Counts starting from a given stone the number of equal stones
     * which are horizontally aligned.
     *
     * @param row the row number
     * @param col the column number
     * @return the number of horizontally matching stones or 0 if the given cell is empty
     */
    public int countHorizontally(int row, int col) {
        // TODO: implement based on documentation and tests

        Stone origin = getStone(row, col);

        if (origin == Stone.None) {
            return 0;
        }

        int count = 1;

        for (int i = col + 1; i < cols; i++) {
            if (origin != getStone(row, i)) {
                break;
            }

            count++;
        }

        for (int i = col - 1; i >= 0; i--) {
            if (origin != getStone(row, i)) {
                break;
            }

            count++;
        }

        return count;
    }

    /**
     * Counts starting from a given stone the number of equal stones
     * which are vertically aligned.
     *
     * @param row the row number
     * @param col the column number
     * @return the number of vertically matching stones or 0 if the given cell is empty
     */
    public int countVertically(int row, int col) {
        Stone stone = getStone(row, col);
        if (stone == Stone.None) {
            return 0;
        }
        int count = 1;
        for (int rowDir = 1; row + rowDir < rows && getStone(row + rowDir, col) == stone; rowDir++) {
            count++;
        }
        for (int rowDir = -1; row + rowDir >= 0 && getStone(row + rowDir, col) == stone; rowDir--) {
            count++;
        }
        return count;
    }

    /**
     * Counts starting from a given stone the number of equal stones
     * which are right-diagonally aligned.
     *
     * @param row the row number
     * @param col the column number
     * @return the number of right-diagonally matching stones or 0 if the given cell is empty
     */
    public int countDiagonallyRight(int row, int col) {
        // TODO: finish implementation to match documentation and tests
        Stone stone = getStone(row, col);

        if (stone == Stone.None) {
            return 0;
        }

        int count = 1;
        for (int dir = 1; row + dir < rows && col + dir < cols && getStone(row + dir, col + dir) == stone; dir++) {
            count++;
        }
        for (int dir = -1; row + dir >= 0 && col - dir >= 0 && getStone(row + dir, col - dir) == stone; dir--) {
            count++;
        }
        return count;
    }

    /**
     * Counts starting from a given stone the number of equal stones
     * which are left-diagonally aligned.
     *
     * @param row the row number
     * @param col the column number
     * @return the number of left-diagonally matching stones or 0 if the given cell is empty
     */
    public int countDiagonallyLeft(int row, int col) {
        // TODO: finish implementation to match documentation and tests
        Stone stone = getStone(row, col);

        if (stone == Stone.None) {
            return 0;
        }

        int count = 1;
        for (int dir = 1; row + dir < rows && col - dir >= 0 && getStone(row + dir, col - dir) == stone; dir++) {
            count++;
        }
        for (int dir = -1; row + dir >= 0 && col - dir < cols && getStone(row + dir, col - dir) == stone; dir--) {
            count++;
        }
        return count;
    }
}
