import four.game.Board;
import four.game.Stone;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class BoardTest {
    private Board field;
    private int boardRows;
    private int boardCols;

    @BeforeEach
    void setUp() {
        boardRows = 6;
        boardCols = 7;
        field = new Board(boardRows, boardCols);
    }

    @Test
    public void testMaxBoardDimensions() {
        Board board = new Board(9, 9);
        for (int r = 0; r < 9; r++) {
            for (int c = 0; c < 9; c++) {
                assertTrue(board.isValidCell(r, c));
            }
        }
    }

    @Test
    public void testInvalidBoardDimensions() {
        // TODO: fix constructor implementation to make this test work
        assertThrows(IllegalArgumentException.class, () -> new Board(0, 1));
        assertThrows(IllegalArgumentException.class, () -> new Board(6, -1));
        assertThrows(IllegalArgumentException.class, () -> new Board(8, Integer.MAX_VALUE));
        assertThrows(IllegalArgumentException.class, () -> new Board(10, 9));
    }

    @Test
    public void testFieldInitialization() {
        // TODO: test that field initially only contains empty cells (Stone.None)
        for (int r = 0; r < boardRows; r++) {
            for (int c = 0; c < boardCols; c++) {
                assertEquals(Stone.None, field.getStone(r, c));
            }
        }
    }

    @Test
    public void testGetStone() {
        int row = field.setStone(1, Stone.O);
        assertEquals(Stone.O, field.getStone(row, 1));
    }

    @Test
    public void testGetStoneInvalid() {
        // TODO: test Board.getStone with illegal arguments (use at least 3 different illegal parameter combinations)
        assertThrows(IllegalArgumentException.class, () -> field.getStone(-1, 0));
        assertThrows(IllegalArgumentException.class, () -> field.getStone(0, -1));
        assertThrows(IllegalArgumentException.class, () -> field.getStone(0, boardCols));
        assertThrows(IllegalArgumentException.class, () -> field.getStone(boardRows, 0));
    }

    @Test
    public void testSetStoneValid() {
        int row = field.setStone(1, Stone.O);
        assertEquals(Stone.O, field.getStone(row, 1));
    }

    @Test
    public void testSetStoneInvalid() {
        // TODO: test Board.setStone with invalid column (use at least 2 different invalid column values) and invalid stone
        assertThrows(IllegalArgumentException.class, () -> field.setStone(-1, Stone.O));
        assertThrows(IllegalArgumentException.class, () -> field.setStone(boardCols, Stone.O));
        assertThrows(IllegalArgumentException.class, () -> field.setStone(0, Stone.None));
    }

    @Test
    public void testIsValidCellTrue() {
        // TODO: test with least 3 different parameter combinations
        assertTrue(field.isValidCell(0, 0));
        assertTrue(field.isValidCell(0, boardCols - 1));
        assertTrue(field.isValidCell(boardRows - 1, 0));
    }

    @Test
    public void testIsValidCellFalse() {
        // TODO: test with least 3 different parameter combinations
        assertFalse(field.isValidCell(-1, 0));
        assertFalse(field.isValidCell(0, -1));
        assertFalse(field.isValidCell(boardRows, 0));
        assertFalse(field.isValidCell(0, boardCols));
    }

    @Test
    public void testIsValidMoveTrue() {
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.O);
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.X);
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.O);
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.X);
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.O);
        assertTrue(field.isValidMove(0));
        field.setStone(0, Stone.X);
    }

    @Test
    public void testIsValidMoveFalse() {
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.X);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.X);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.X);

        assertFalse(field.isValidMove(0));
        assertFalse(field.isValidMove(-1));
        assertFalse(field.isValidMove(10));
    }

    @Test
    public void testGetNextFreeRow() {
        // TODO: test with at least 3 calls to getNextFreeRow
        assertEquals(boardRows - 1, field.getNextFreeRow(0));
        assertEquals(boardRows - 1, field.getNextFreeRow(1));
        assertEquals(boardRows - 1, field.getNextFreeRow(2));
    }

    @Test
    public void testGetNextFreeRowFull() {
        // TODO: test getNextFreeRow if column is full
        for (int i = 0; i < boardRows; i++) {
            field.setStone(0, Stone.O);
        }

        assertEquals(-1, field.getNextFreeRow(0));
    }

    @Test
    public void testIsEmptyTrue() {
        // TODO: test whether all fields are initially empty
        for (int i = 0; i < boardRows; i++) {
            for (int j = 0; j < boardCols; j++) {
                assertTrue(field.isEmpty(i, j));
            }
        }
    }

    @Test
    public void testIsEmptyFalse() {
        // TODO: test isEmpty on field with stone
        field.setStone(0, Stone.O);
        assertFalse(field.isEmpty(boardRows - 1, 0));
    }

    @Test
    public void testIsFullTrue() {
        // TODO: test isFull on board where every stone is set
        for (int i = 0; i < boardRows; i++) {
            for (int j = 0; j < boardCols; j++) {
                field.setStone(j, Stone.O);
            }
        }

        assertTrue(field.isFull());
    }

    @Test
    public void testIsFullFalse() {
        // TODO: set stones on every field and test before each move whether the field is full
        for (int i = 0; i < boardRows; i++) {
            for (int j = 0; j < boardCols; j++) {
                assertFalse(field.isFull());

                field.setStone(j, Stone.O);
            }
        }
    }

    @Test
    public void testHasFourConnectedTrue() {
        // TODO: test hasFourConnected (returning true) with at least 3 calls
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.O);

        assertTrue(field.hasFourConnected(boardRows - 1, 0));
        assertTrue(field.hasFourConnected(boardRows - 2, 0));
        assertTrue(field.hasFourConnected(boardRows - 3, 0));
        assertTrue(field.hasFourConnected(boardRows - 4, 0));
    }

    @Test
    public void testHasFourConnectedFalse() {
        // TODO: test hasFourConnected (returning false) with at least 3 calls
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.O);
        field.setStone(0, Stone.X);

        assertFalse(field.hasFourConnected(0, 0));
        assertFalse(field.hasFourConnected(1, 0));
        assertFalse(field.hasFourConnected(2, 0));
        assertFalse(field.hasFourConnected(3, 0));
    }

    @Test
    public void testCountHorizontally() {
        // TODO: test countHorizontally with at least 2 calls
        field.setStone(0, Stone.O);
        assertEquals(1, field.countHorizontally(boardRows - 1, 0));

        field.setStone(1, Stone.O);
        assertEquals(2, field.countHorizontally(boardRows - 1, 0));
    }

    @Test
    public void testCountHorizontallyEmpty() {
        assertEquals(0, field.countHorizontally(0, 0));
    }

    @Test
    public void testCountVertically() {
        // TODO: test countVertically with at least 2 calls
        field.setStone(0, Stone.O);
        assertEquals(1, field.countVertically(boardRows - 1, 0));

        field.setStone(0, Stone.O);
        assertEquals(2, field.countVertically(boardRows - 1, 0));
    }

    @Test
    public void testVerticallyEmpty() {
        assertEquals(0, field.countVertically(5, 6));
    }

    @Test
    public void testCountDiagonallyRight() {
        // TODO: test countDiagonallyRight with at least 2 calls
        field.setStone(1, Stone.X);
        field.setStone(0, Stone.O);
        assertEquals(1, field.countDiagonallyRight(boardRows - 1, 0));

        field.setStone(1, Stone.O);
        assertEquals(2, field.countDiagonallyRight(boardRows - 1, 0));
    }

    @Test
    public void testCountDiagonallyRightEmpty() {
        assertEquals(0, field.countDiagonallyRight(1, 4));
    }

    @Test
    public void testCountDiagonallyLeft() {
        // TODO: test countDiagonallyLeft with at least 2 calls
        field.setStone(0, Stone.O);
        assertEquals(1, field.countDiagonallyRight(boardRows - 1, 0));

        field.setStone(1, Stone.X);
        field.setStone(1, Stone.O);
        assertEquals(2, field.countDiagonallyRight(boardRows - 1, 0));
    }

    @Test
    public void testDiagonallyLeftEmpty() {
        assertEquals(0, field.countDiagonallyLeft(0, 1));
    }
}
