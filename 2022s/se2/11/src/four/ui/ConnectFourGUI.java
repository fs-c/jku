package four.ui;

import four.game.*;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;

public class ConnectFourGUI {
    private Game game;
    private JFrame frame;
    private JButton[] buttons;

    public void start() {
        game = new Game(new Player("X", Stone.X), new Player("O", Stone.O), 6, 7);
        Board board = game.getBoard();

        frame = new JFrame("Connect Four");

        frame.setLayout(new BorderLayout());
        frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);

        // menu bar setup
        JMenuBar menuBar = new JMenuBar();
        frame.setJMenuBar(menuBar);
        JMenu menu = menuBar.add(new JMenu("File"));
        int nCols = board.getCols();

        // add control buttons
        JPanel buttonPanel = new JPanel(new GridLayout(1, nCols));
        buttons = new JButton[nCols];

        // button row
        for (int c = 0; c < buttons.length; c++) {
            final int col = c;
            JButton button = new JButton(String.valueOf(col + 1));
            // TODO: add action listener to make move

            button.addActionListener((e) -> {
                game.makeMove(col);
            });

            buttons[c] = button;
            buttonPanel.add(button);
        }

        frame.add(buttonPanel, BorderLayout.NORTH);

        BoardPanel boardPanel = new BoardPanel(game);
        frame.add(boardPanel, BorderLayout.CENTER);

        // message panel
        JPanel messagePanel = new JPanel(new BorderLayout());
        messagePanel.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.BLACK, 1, true), "Messages"));
        JLabel status = new JLabel();
        status.setPreferredSize(new Dimension(status.getPreferredSize().width, 50));

        messagePanel.add(status, BorderLayout.CENTER);
        frame.add(messagePanel, BorderLayout.SOUTH);

        // TODO: add restart menu item
        JMenuItem restartItem = new JMenuItem("Restart");
        restartItem.addActionListener((e) -> {
            game.restart();

            status.setText("Restarted");

            enableInputs(true);
        });
        menu.add(restartItem);

        JMenuItem exitItem = new JMenuItem("Exit");
        exitItem.addActionListener(e -> frame.dispose());
        menu.add(exitItem);

        // TODO: add game listener to set status and handle game ending events
        game.addGameListener(new GameListener() {
            @Override
            public void moveCompleted(GameEvent event) {
                final int col = event.getCol();

                for (int row = 0; row < board.getRows(); row++) {
                    if (board.isEmpty(row, col)) {
                        return;
                    }
                }

                buttons[col].setEnabled(false);

                status.setText(String.format("Set stone in %d/%d", event.getRow(), event.getCol()));
            }

            @Override
            public void gameStateChanged(GameEvent event) {
                final Game.State state = event.getState();
                final String message = (
                        state == Game.State.OWon ? "O won" :
                        state == Game.State.XWon ? "X won" :
                        state == Game.State.Draw ? "Draw" : ""
                );

                if (message.length() != 0) {
                    handleGameOver(message);
                }
            }
        });

        frame.pack();
        frame.setVisible(true);
    }

    /**
     * Enables or disables the input buttons.
     *
     * @param enabled the flag to determine the button state
     */
    private void enableInputs(boolean enabled) {
        for (JButton button : buttons) {
            button.setEnabled(enabled);
        }
    }

    /**
     * Ends the game by disabling the input buttons and showing a game over message.
     *
     * @param message the game over message to show
     */
    private void handleGameOver(String message) {
        enableInputs(false);
        JOptionPane.showMessageDialog(frame, message, "Game Over!", JOptionPane.INFORMATION_MESSAGE);
    }
}
