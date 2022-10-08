package four.game;

/**
 * Represents the state of a cell in a Connect Four game.
 * A cell either contains a stone ({@link Stone#X}/{@link Stone#O})
 * or is {@linkplain Stone#None} empty.
 */
public enum Stone {
    None, X, O;

    /**
     * Returns a textual representation of the stone.
     *
     * @return the stone as a string
     */
    public String outputString() {
        if (this == None) {
            return " - ";
        } else {
            return " " + this + " ";
        }
    }
}
