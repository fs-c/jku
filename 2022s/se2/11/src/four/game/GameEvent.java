package four.game;

import four.game.Game;

import java.util.EventObject;

public class GameEvent extends EventObject {
    private final Game.State state;
    private final int row;
    private final int col;

    public GameEvent(Game source, Game.State state, int row, int col) {
        super(source);

        this.state = state;
        this.row = row;
        this.col = col;
    }

    public GameEvent(Game source, Game.State state) {
        this(source, state, -1, -1);
    }

    public Game.State getState() {
        return state;
    }

    public int getRow() {
        return row;
    }

    public int getCol() {
        return col;
    }
}
