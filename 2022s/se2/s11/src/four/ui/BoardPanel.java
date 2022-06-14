package four.ui;

import four.game.*;

import java.awt.*;

import javax.swing.*;
import javax.swing.border.LineBorder;

public class BoardPanel extends JPanel {
    public static final Color X_COLOR = Color.RED;
    public static final Color O_COLOR = new Color(110, 110, 255);
    private static final Color BG_COLOR = Color.WHITE;
    private static final Color GRID_COLOR = Color.DARK_GRAY;
    private static final int BORDER_THICKNESS = 5;

    private static final int PREFERRED_CELL_SIZE = 50;

    private final Board board;

    public BoardPanel(Game game) {
        this.board = game.getBoard();
        // sets a custom border that changes color based on current game state or player
        setBorder(new LineBorder(Color.WHITE, 7) {
            @Override
            public void paintBorder(final Component c, final Graphics g, final int x, final int y, final int width, final int height) {
                g.setColor(getBorderColor(game.getGameState()));
                for (int i = 0; i < BORDER_THICKNESS; i++) {
                    g.drawRect(x + i, y + i, width - i - i, height - i - i);
                }
            }
        });

        // TODO: repaint on any GameEvent
        game.addGameListener(new GameListener() {
            @Override
            public void moveCompleted(GameEvent event) {
                repaint();
            }

            @Override
            public void gameStateChanged(GameEvent event) {
                repaint();
            }
        });

        setPreferredSize(new Dimension(board.getCols() * PREFERRED_CELL_SIZE, board.getRows() * PREFERRED_CELL_SIZE));
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        // TODO: draw stones

        final int cellWidth = getWidth() / board.getCols();
        final int cellHeight = getHeight() / board.getRows();

        for (int row = 0; row < board.getRows(); row++) {
            for (int col = 0; col < board.getCols(); col++) {
                final Stone stone = board.getStone(row, col);

                g.setColor(Color.BLACK);
                g.drawOval(col * cellWidth, row * cellHeight, cellWidth, cellHeight);

                if (stone == Stone.X || stone == Stone.O) {
                    g.setColor(stone == Stone.X ? Color.BLUE : Color.RED);
                    g.fillOval(col * cellWidth, row * cellHeight, cellWidth, cellHeight);
                }
            }
        }
    }

    /**
     * Gets the drawing color for the given stone.
     *
     * @param stone the stone
     * @return the color that should be used to draw the given stone
     */
    private static Color getColor(Stone stone) {
        return switch (stone) {
            case O -> O_COLOR;
            case X -> X_COLOR;
            case None -> BG_COLOR;
        };
    }

    /**
     * Gets the border color based on the given game state.
     *
     * @param gameState the game state
     * @return the color that should be used to paint the border
     */
    private static Color getBorderColor(Game.State gameState) {
        return switch (gameState) {
            case OsTurn, OWon -> O_COLOR;
            case XsTurn, XWon -> X_COLOR;
            case Draw -> Color.ORANGE;
        };
    }
}
