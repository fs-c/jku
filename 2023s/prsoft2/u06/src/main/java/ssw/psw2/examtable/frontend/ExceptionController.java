package ssw.psw2.examtable.frontend;

import javafx.application.Platform;
import javafx.scene.control.Alert;

final class ExceptionController {

    static void displayError(Throwable t) {
        Platform.runLater(() -> {
            final Alert alert = new Alert(Alert.AlertType.ERROR);
            alert.setHeaderText(t.getClass().getSimpleName());
            alert.setContentText(t.getMessage());
            alert.show();
        });
    }

    private ExceptionController() {
        // no instances
    }
}
