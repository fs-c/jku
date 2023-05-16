package ssw.psw2.examtable;

import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.util.converter.IntegerStringConverter;
import ssw.psw2.examtable.model.ExamTableModel;
import ssw.psw2.examtable.model.Result;

import java.io.IOException;

public class Controller {
	public Button addResultButton;
	public Button removeResultButton;
	@FXML
	private TableView tableView;

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
		initializeTable();

		initializeButtons();
	}

	void initializeTable() {
		var idCol = new TableColumn<Result, String>("ID");
		idCol.setCellValueFactory(new PropertyValueFactory<>("studentId"));

		var lastNameCol = new TableColumn<Result, String>("Name");
		lastNameCol.setCellValueFactory(new PropertyValueFactory<>("studentLastName"));

		var firstNameCol = new TableColumn<Result, String>("First");
		firstNameCol.setCellValueFactory(new PropertyValueFactory<>("studentFirstName"));

		var pointsCol = new TableColumn<Result, Integer>("Points");
		pointsCol.setCellValueFactory(new PropertyValueFactory<>("points"));
		pointsCol.setCellFactory(TextFieldTableCell.forTableColumn(new IntegerStringConverter()));
		pointsCol.setOnEditCommit((e) -> {
			int row = e.getTablePosition().getRow();

			try {
				examTableModel.results.get(row).setPoints(e.getNewValue());
			} catch (IllegalArgumentException ignored) {

			}

			tableView.refresh();
		});

		var gradeCol = new TableColumn<Result, String>("Grade");
		gradeCol.setCellValueFactory(new PropertyValueFactory<>("grade"));

		tableView.getColumns().addAll(idCol, lastNameCol, firstNameCol, pointsCol, gradeCol);

		tableView.setItems(examTableModel.results);

		tableView.setEditable(true);
	}

	void initializeButtons() {
		removeResultButton.setOnAction((e) -> {
			ObservableList<Integer> selectedIndices = tableView.getSelectionModel().getSelectedIndices();

			for (int index : selectedIndices) {
				examTableModel.results.remove(index);
			}
		});

		addResultButton.setOnAction((e) -> {
			try {
				final Stage popup = new Stage();

				final FXMLLoader loader = new FXMLLoader(getClass().getResource("addResults.fxml"));
				final Parent root = loader.load();

				AddController controller = loader.getController();
				controller.setExamTableModel(examTableModel);
				controller.setStage(popup);

				popup.initModality(Modality.APPLICATION_MODAL);
				popup.initOwner(this.primaryStage);

				popup.setTitle("Add Result");
				popup.setScene(new Scene(root));
				popup.show();
			} catch (IOException ex) {
				throw new RuntimeException(ex);
			}
		});
	}
}
