package four.game;

import java.util.ArrayList;

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

    // TODO: add listeners field
    private ArrayList<GameListener> listeners;

    /**
     * Creates a new ConnectFour game with the given properties.
     *
     * @param xPlayer the first player
     * @param oPlayer the second player
     * @param rows the number of rows the board should have
     * @param columns the number of columns the board should have
     * @throws IllegalArgumentException if one of the given players has an invalid stone assigned
     * @throws IllegalStateException if the given players have the same stone assigned
     */
    public Game(Player xPlayer, Player oPlayer, int rows, int columns) {
        if (xPlayer.stone() == Stone.None || oPlayer.stone() == Stone.None) {
            throw new IllegalArgumentException("Players must have a valid stone assigned");
        } else if (xPlayer.stone() == oPlayer.stone()) {
            throw new IllegalStateException("Players must play with different stones");
        }

        this.board = new Board(rows, columns);
        this.xPlayer = xPlayer;
        this.oPlayer = oPlayer;
        this.gameState = State.OsTurn;
        this.current = oPlayer;
        // TODO: initialize listeners list
        this.listeners = new ArrayList<>();
    }

    /**
     * Gets the ConnectFour board.
     *
     * @return the currently played board
     */
    public Board getBoard() {
        return board;
    }

    /**
     * Gets the current game state.
     *
     * @return the current game state
     */
    public Game.State getGameState() {
        return gameState;
    }

    /**
     * Represents the different game states.
     */
    public enum State {
        XsTurn, OsTurn, XWon, OWon, Draw
    }

    /**
     * Places a stone in the given column and updates the game state accordingly.
     *
     * @param col the column number
     */
    public void makeMove(int col) {
        // TODO: fire event when move is completed
        int row = board.setStone(col, current.stone());
        updateGameState(row, col);

        fireMoveCompleted(row, col);
    }

    /**
     * Restarts the game by clearing the board.
     */
    public void restart() {
        board.clear();
        setGameState(State.OsTurn);
        current = oPlayer;
    }

    private void updateGameState(int row, int col) {
        if (board.hasFourConnected(row, col)) {
            if (current.stone() == Stone.X) {
                setGameState(State.XWon);
            } else {
                setGameState(State.OWon);
            }
        } else if (board.isFull()) {
            setGameState(State.Draw);
        } else {
            changePlayer();
        }
    }

    private void changePlayer() {
        if (current.stone() == Stone.X) {
            current = oPlayer;
            setGameState(State.OsTurn);
        } else {
            current = xPlayer;
            setGameState(State.XsTurn);
        }
    }

    private void setGameState(State state) {
        // TODO: fire event to signal state change
        gameState = state;

        fireGameStateChanged();
    }

    // TODO: implement event firing mechanisms
    void fireGameStateChanged() {
        var event = new GameEvent(this, gameState);

        listeners.forEach((l) -> l.gameStateChanged(event));
    }

    void fireMoveCompleted(int row, int col) {
        var event = new GameEvent(this, gameState, row, col);

        listeners.forEach((l) -> l.moveCompleted(event));
    }

    // TODO: implement add/remove listener methods
    public void addGameListener(GameListener listener) {
        listeners.add(listener);
    }

    public void removeGameListener(GameListener listener) {
        listeners.remove(listener);
    }
}
