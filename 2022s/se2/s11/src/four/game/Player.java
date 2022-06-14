package four.game;

/**
 * Represents a ConnectFour player.
 * A player is assigned a specific {@link #name} and {@link #stone}.
 */
public record Player(String name, Stone stone) {
    @Override
    public String toString() {
        return "Player " + name;
    }
}
