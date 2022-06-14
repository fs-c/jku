package four.game;

import four.game.GameEvent;

import java.util.EventListener;

public interface GameListener extends EventListener {
    void moveCompleted(GameEvent event);

    void gameStateChanged(GameEvent event);
}
