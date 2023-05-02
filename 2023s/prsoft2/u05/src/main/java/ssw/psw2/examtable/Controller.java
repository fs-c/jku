package ssw.psw2.examtable;

import javafx.fxml.FXML;
import javafx.stage.Stage;
import ssw.psw2.examtable.model.ExamTableModel;

public class Controller {

	// TODO define JavaFX components

	private final ExamTableModel examTableModel;
	private Stage primaryStage;

	public Controller(ExamTableModel model) {
		this.examTableModel = model;
		this.primaryStage = null;
	}

	public Controller() {
		this.examTableModel = new ExamTableModel();
		this.primaryStage = null;
	}

	public void setPrimaryStage(Stage stage) {
		this.primaryStage = stage;
	}

	@FXML
	void initialize() {
		// TODO
	}

}
