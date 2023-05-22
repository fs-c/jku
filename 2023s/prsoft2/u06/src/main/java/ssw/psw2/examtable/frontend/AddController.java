package ssw.psw2.examtable.frontend;

import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.paint.Color;
import javafx.stage.Stage;
import ssw.psw2.examtable.common.ExamTableModel;

public class AddController {
	@FXML
	private ChoiceBox<Integer> snChoice;

	@FXML
	private Button addButton;
	
	@FXML
	private Label validInputLabel;

	@FXML private TextField studentIDField;

	@FXML private TextField studentNameField;

	@FXML private TextField studentFirstNameField;

	public void init(ExamTableModel model) {
		addButton.setOnAction(evt -> {
			String studentID = studentIDField.textProperty().get();
			String studentName = studentNameField.textProperty().get();
			String studentFirstName = studentFirstNameField.textProperty().get();
			
			if(studentID.equals("") || studentName.equals("") || studentFirstName.equals("")) {
				validInputLabel.textProperty().set("Empty fields!");
				validInputLabel.setTextFill(Color.web("red"));
				return;
			}
			
			try{
				model.addResult(studentID, studentName, studentFirstName);
			} catch(Exception e) {
				validInputLabel.textProperty().set(e.getMessage());
				validInputLabel.setTextFill(Color.web("red"));
				return;
			}
			((Stage)addButton.getScene().getWindow()).close();
		});
	}

}
