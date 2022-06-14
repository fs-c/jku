package four;

import four.ui.ConnectFourGUI;

import javax.swing.*;

public class SwingMain {
    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> new ConnectFourGUI().start());
    }
}
