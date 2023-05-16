package ssw.psw2.examtable;
	
import java.io.IOException;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.stage.Stage;
import javafx.scene.Parent;
import javafx.scene.Scene;
import ssw.psw2.examtable.model.ExamTableModel;
import ssw.psw2.examtable.model.Result;
import ssw.psw2.examtable.model.TestData;

public class Main extends Application {
	@Override
	public void start(Stage primaryStage) throws IOException {
		final FXMLLoader loader = new FXMLLoader(getClass().getResource("examTableUI.fxml"));
		final Parent root = loader.load();

		Controller controller = loader.getController();
		controller.setPrimaryStage(primaryStage);

		primaryStage.setTitle("Grades");
		primaryStage.setScene(new Scene(root));
		primaryStage.show();

		// todo: close db connection at some point (shutdown hook?)
	}
	
	public static void main(String[] args) {
		launch(args);
	}
}