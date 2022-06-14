package four.game;

import inout.In;
import inout.Out;

/**
 * Represents a ConnectFour player.
 * A player is assigned a specific {@link #name} and {@link #stone}.
 */
public record Player(String name, Stone stone) {

    /**
     * Reads the next move for this player from the console.
     * This is repeated until a {@linkplain Board#isValidMove(int) valid move} is specified.
     *
     * @param board the board that is played
     * @return the target column number
     */
    public int getMove(Board board) {
        int col = readColumn();
        while (!board.isValidMove(col - 1)) {
            Out.println("Invalid move: " + col);
            col = readColumn();
        }
        return col - 1;
    }

    private int readColumn() {
        int col;
        Out.println("Input column for " + this);
        col = In.readInt();
        if (!In.done()) {
            In.readLine();
        }
        Out.println();
        return col;
    }

    @Override
    public String toString() {
        return "Player " + name;
    }
}
