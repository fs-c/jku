package four.game;

import inout.Out;

/**
 * Implements the game <a href="https://en.wikipedia.org/wiki/Connect_Four">Connect Four</a>
 * for two {@linkplain Player players} on a {@link Board} with custom dimensions.
 */
public class Game {
    private final Board board;
    private State gameState;

    private final Player xPlayer;
    private final Player oPlayer;
    private Player current;

    // TODO: complete documentation based on implementation below
    /**
     * Creates a new ConnectFour game with the given properties.
     *
     * @param xPlayer the first player
     * @param oPlayer the second player
     * @param rows the number of rows the board should have
     * @param columns the number of columns the board should have
     *
     * @throws IllegalArgumentException if one of the players doesn't have a stone or if the players have the same stone
     */
    public Game(Player xPlayer, Player oPlayer, int rows, int columns) {
        this.board = new Board(rows, columns);

        // TODO: check that players do not have Stone.None as stone; otherwise throw IllegalArgumentException
        // TODO: check that players have different stones; otherwise throw IllegalStateException

        if (xPlayer.stone() == Stone.None || oPlayer.stone() == Stone.None) {
            throw new IllegalArgumentException("Player has no stone");
        }

        if (xPlayer.stone() == oPlayer.stone()) {
            throw new IllegalStateException("Players have the same stone");
        }

        this.xPlayer = xPlayer;
        this.oPlayer = oPlayer;
    }

    /**
     * Represents the different game states.
     */
    public enum State {
        XsTurn, OsTurn, XWon, OWon, Draw
    }

    /**
     * Starts the ConnectFour game.
     * <br/>
     * In each turn, a {@linkplain Player#getMove(Board) move is requested} from the {@link #current} player and the board is {@linkplain Board#print() printed}.
     * The game stops if a player has won ({@link State#XWon}/{@link State#OWon}) or if it is a draw ({@link State#Draw}).
     */
    public void play() {
        Out.println("Connect Four");
        Out.println();
        gameState = State.OsTurn;
        current = oPlayer;
        while (gameState != State.Draw && gameState != State.XWon && gameState != State.OWon) {
            printGameState();
            int col = current.getMove(board);
            int row = board.setStone(col, current.stone());
            updateGameState(row, col);
        }
        printGameState();
        if (gameState == State.XWon) {
            Out.println("Game finished. " + xPlayer + " has won! ");
        } else if (gameState == State.OWon) {
            Out.println("Game finished. " + oPlayer + " has won! ");
        } else {
            Out.println("Game finished. It's a draw! ");
        }
    }

    private void printGameState() {
        board.print();
        Out.println("GameState: " + gameState);
        Out.println();
    }

    private void updateGameState(int row, int col) {
        if (board.hasFourConnected(row, col)) {
            if (current.stone() == Stone.X) {
                gameState = State.XWon;
            } else {
                gameState = State.OWon;
            }
        } else if (board.isFull()) {
            gameState = State.Draw;
        } else {
            changePlayer();
        }
    }

    private void changePlayer() {
        if (current.stone() == Stone.X) {
            current = oPlayer;
            gameState = State.OsTurn;
        } else {
            current = xPlayer;
            gameState = State.XsTurn;
        }
    }
}
