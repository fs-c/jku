package ssw.psw2.examtable.frontend;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.util.StringConverter;
import ssw.psw2.examtable.common.ExamTableModel;
import ssw.psw2.examtable.common.Result;
import ssw.psw2.examtable.common.ResultChangedListener;

import java.io.IOException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;

public class Controller {

    @FXML
    private TableView<Result> tableView;
    @FXML
    private TableColumn<Result, String> studentIDColumn;
    @FXML
    private TableColumn<Result, String> studentNameColumn;
    @FXML
    private TableColumn<Result, String> studentFirstColumn;
    @FXML
    private TableColumn<Result, Integer> pointsColumn;
    @FXML
    private TableColumn<Result, String> gradeColumn;

    @FXML
    private Button addButton;
    @FXML
    private Button removeButton;

    private ExamTableModel examTableModel;
    private Stage primaryStage;
    private ResultChangedListener resultChangedListener;

    public Controller() {
        this.examTableModel = null;
        this.primaryStage = null;
        this.resultChangedListener = null;
    }

    public void setPrimaryStage(Stage stage) {
        this.primaryStage = stage;
    }

    @FXML
    void initialize() {
        tableView.setEditable(true);
        tableView.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);

        // non-editable columns
        studentIDColumn.setCellValueFactory(new PropertyValueFactory<Result, String>("id"));
        studentNameColumn.setCellValueFactory(new PropertyValueFactory<Result, String>("name"));
        studentFirstColumn.setCellValueFactory(new PropertyValueFactory<Result, String>("firstName"));

        // exam points column
        setEditProperties(pointsColumn);

        // buttons
        setupButtons();

        // calculated columns
        gradeColumn.setCellValueFactory(new PropertyValueFactory<Result, String>("grade"));
    }

    public void postInitialize(ExamTableModel examTableModel) {
        if (this.examTableModel == null) {
            this.examTableModel = examTableModel;

            try {
                resultChangedListener = new ModelChangedListener();

                this.examTableModel.addResultChangedListener(resultChangedListener);
                tableView.getItems().addAll(examTableModel.getResults());
            } catch (RemoteException e) {
                ExceptionController.displayError(e);
            }
        }
    }

    public void onClose() {
        try {
            examTableModel.removeResultChangedListener(resultChangedListener);
        } catch (RemoteException e) {
            ExceptionController.displayError(e);
        }
    }

    private void setupButtons() {
        addButton.setOnAction(event -> {
            try {
                final FXMLLoader loader = new FXMLLoader(getClass().getResource("addResults.fxml"));
                final Parent root = loader.load();

                final AddController controller = loader.getController();
                controller.init(examTableModel);

                final Stage popupStage = new Stage();
                popupStage.setScene(new Scene(root));
                popupStage.initOwner(primaryStage);
                popupStage.initModality(Modality.APPLICATION_MODAL);
                popupStage.setTitle("Add Result");
                popupStage.show();

            } catch (IOException e) {
                // ignored, this should not happen for an included resource
                e.printStackTrace();
            }
        });

        removeButton.setOnAction(event -> {
            final Result selectedItem = tableView.getSelectionModel().getSelectedItem();

            // do nothing if no item is selected
            if (selectedItem != null) {
                try {
                    examTableModel.removeResult(selectedItem.getId());
                } catch (RemoteException e) {
                    ExceptionController.displayError(e);
                }
            }
        });
    }

    private void setEditProperties(TableColumn<Result, Integer> col) {
        col.setCellFactory(TextFieldTableCell.forTableColumn(new StringConverter<Integer>() {
            @Override
            public String toString(Integer object) {
                return object != null ? object.toString() : "";
            }

            @Override
            public Integer fromString(String string) {
                try {
                    return Integer.parseInt(string);
                } catch (NumberFormatException e) {
                    return null;
                }
            }
        }));

        col.setOnEditCommit(evt -> {
            Integer newVal = evt.getNewValue();
            // would be cleaner with condition check in a custom property or its setter
            if (newVal == null
                    || (newVal < Result.MIN_POINTS || newVal > Result.MAX_POINTS) && newVal != Result.UNDEFINED) {
                tableView.refresh();
                return;
            }
            Result result = evt.getTableView().getItems().get(evt.getTablePosition().getRow());

            try {
                examTableModel.updateResult(result.getId(), newVal);
            } catch (RemoteException e) {
                ExceptionController.displayError(e);
            }
        });

        col.setCellValueFactory(new PropertyValueFactory<>("points"));
    }

    private class ModelChangedListener extends UnicastRemoteObject implements ResultChangedListener {
        ModelChangedListener() throws RemoteException {
            super();
        }

        @Override
        public void onResultAdded(Result result) {
            tableView.getItems().add(result);
        }

        @Override
        public void onResultChanged(String resultID, int newPoints) {
            for (Result r : tableView.getItems()) {
                if (r.getId().equals(resultID)) {
                    r.setPoints(newPoints);
                    tableView.refresh();
                    return;
                }
            }
        }

        @Override
        public void onResultRemoved(String resultID) {
            tableView.getItems().removeIf((r) -> r.getId().equals(resultID));
        }

        @Override
        public void onGeneralRefresh() throws RemoteException {
            tableView.getItems().clear();
            tableView.getItems().addAll(examTableModel.getResults());
        }
    }

}
