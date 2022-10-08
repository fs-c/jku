package four.game;

/**
 * The ConnectFour board that tracks the {@link #field} states.
 */
public class Board {
    private static final int MAX_DIM = 9;

    private final int rows;
    private final int cols;

    private final Stone[][] field;

    /**
     * Creates a new board with the given dimensions and initializes all cells
     * as empty ({@link Stone#None}).
     *
     * @param rows the number of rows
     * @param cols the number of columns
     * @throws IllegalArgumentException if the board dimension are below zero or above {@link #MAX_DIM}
     */
    public Board(int rows, int cols) {
        if (rows <= 0 || cols <= 0) {
            throw new IllegalArgumentException(String.format("Illegal board dimensions - rows: %d, cols: %d", rows, cols));
        } else if (rows > MAX_DIM || cols > MAX_DIM) {
            throw new IllegalArgumentException(String.format("Board dimensions (rows: %d, cols: %d) must not exceed 20x20", rows, cols));
        }

        this.rows = rows;
        this.cols = cols;
        this.field = new Stone[rows][cols];
        clear();
    }

    /**
     * Gets the row count.
     *
     * @return the number of rows
     */
    public int getRows() {
        return rows;
    }

    /**
     * Gets the column count.
     *
     * @return the number of columns
     */
    public int getCols() {
        return cols;
    }

    /**
     * Initializes the field (with {@link Stone#None}).
     */
    public final void clear() {
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                field[r][c] = Stone.None;
            }
        }
    }

    /**
     * Retrieves the stone on the given position.
     *
     * @param row the row number
     * @param col the column number
     * @return the Stone (X, O, None) found in the cell
     * @throws IllegalArgumentException if the given position is out of bounds
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

    /**
     * Drops a stone into a column.
     * <br/>
     * The row to place the stone in is determined using {@link #getNextFreeRow(int)}.
     *
     * @return The index of the row the stone has landed
     * @throws IllegalArgumentException if the given stone is invalid ({@link Stone#None}) or
     * the given column is invalid or full
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

    /**
     * Checks whether the given row and column numbers denote a valid cell on the board.
     *
     * @param row the row number
     * @param col the column number
     * @return {@code true} if the given coordinates are within the board dimensions; {@code false} otherwise
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
        return col >= 0 && col < cols && isEmpty(0, col);
    }

    /**
     * Determines the lowest {@linkplain #isEmpty(int, int) empty} row for the given column number.
     *
     * @param col the column number
     * @return the next free row or -1 if the column is full
     * @throws IllegalArgumentException if the given column is invalid
     */
    public int getNextFreeRow(int col) {
        if (col < 0 || col >= cols) {
            throw new IllegalArgumentException("Invalid column number " + col);
        }
        int r;
        for (r = 0; r < rows; r++) {
            if (!isEmpty(r, col)) {
                break;
            }
        }
        return r - 1;
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

    /**
     * Checks if starting from a given field, at least four equal stones are aligned
     * vertically, horizontally or diagonally.
     *
     * @param row the row number
     * @param col the column number
     * @return {@code true} if there are at least 4 connected stones in either direction; {@code false} otherwise
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
        Stone stone = getStone(row, col);
        if (stone == Stone.None) {
            return 0;
        }
        int count = 1;
        for (int colDir = 1; col + colDir < cols && getStone(row, col + colDir) == stone; colDir++) {
            count++;
        }
        for (int colDir = -1; col + colDir >= 0 && getStone(row, col + colDir) == stone; colDir--) {
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
        Stone stone = getStone(row, col);
        if (stone == Stone.None) {
            return 0;
        }
        int count = 1;
        for (int dir = 1; row + dir < rows && col + dir < cols && getStone(row + dir, col + dir) == stone; dir++) {
            count++;
        }
        for (int dir = -1; row + dir >= 0 && col + dir >= 0 && getStone(row + dir, col + dir) == stone; dir--) {
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
