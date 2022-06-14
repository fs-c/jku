package four;

import four.game.Game;
import four.game.Stone;
import four.game.Player;

public class ConnectFourMain {
    public static void main(String[] args) {
        Game game = new Game(new Player("X", Stone.X), new Player("O", Stone.O), 6, 7);
        game.play();
    }
}
