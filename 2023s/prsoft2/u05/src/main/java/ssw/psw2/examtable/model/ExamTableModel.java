package ssw.psw2.examtable.model;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

public class ExamTableModel {
	public ObservableList<Result> results = FXCollections.observableList(TestData.createData());
}
