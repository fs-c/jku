package ssw.psw2.examtable;

import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.stage.Stage;
import ssw.psw2.examtable.model.ExamTableModel;
import ssw.psw2.examtable.model.Result;
import ssw.psw2.examtable.model.Student;

public class AddController {
	private ExamTableModel model;
	private Stage stage;

	@FXML
	private TextField fieldId;
	@FXML
	private TextField fieldLastName;
	@FXML
	private TextField fieldFirstName;
	@FXML
	private Label statusText;
	@FXML
	private Button addButton;

	public void setExamTableModel(ExamTableModel m) {
		model = m;
	}

	public void setStage(Stage s) {
		stage = s;
	}

	@FXML
	public void initialize() {
		addButton.setOnAction((e) -> {
			statusText.setText("");

			var id = fieldId.getText();
			var lastName = fieldLastName.getText();
			var firstName = fieldFirstName.getText();

			if (id.length() == 0 || lastName.length() == 0 || firstName.length() == 0) {
				statusText.setText("Empty fields");

				return;
			}

			model.results.add(new Result(new Student(id, lastName, firstName)));
			stage.close();
		});
	}
}
