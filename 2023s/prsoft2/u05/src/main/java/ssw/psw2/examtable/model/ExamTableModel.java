package ssw.psw2.examtable.model;

import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import ssw.psw2.examtable.ExamDBManager;

import java.util.ArrayList;
import java.util.function.Consumer;

public class ExamTableModel {
	private final ExamDBManager dbManager;
	public ObservableList<Result> results = FXCollections.observableList(new ArrayList<>());

	public ExamTableModel() {
		this.dbManager = new ExamDBManager();
		this.dbManager.openConnection();

		final Consumer<Result> pushResultToDb = (r) -> dbManager.addResult(r.getStudentId(), r.getStudentFirstName(), r.getStudentLastName(), r.getPoints());

		// pull results from database and store them locally. if there are none (empty db), use test data.
		var savedResults = dbManager.getResults();
		if (savedResults.size() != 0) {
			results.addAll(savedResults);
		} else {
			results.addAll(TestData.createData());
			// persist the test data to the db
			results.forEach(pushResultToDb);
		}

		final Consumer<Result> setupResultListener = (r) -> r.getPointsProperty().addListener((ignored, oldValue, newValue) -> {
			System.out.format("points change listener fired: %s -> %s\n", oldValue, newValue);

			dbManager.updateColumn(r.getStudentId(), ExamDBManager.RESULT_POINTS, newValue.toString());
		});

		// add change listeners to the result objects we already have
		results.forEach(setupResultListener);

		// ...and listen to changes on the results list itself
		results.addListener((ListChangeListener<Result>) change -> {
			System.out.println("results change listener fired");

			while (change.next()) {
				// add change listeners to new result objects and add them to the db
				change.getAddedSubList().forEach(setupResultListener.andThen(pushResultToDb));

				// synchronize deletes
				change.getRemoved().forEach((r) -> dbManager.removeResult(r.getStudentId()));

				// todo: handle permutations, i.e. persist ordering (?)
			}
		});
	}
}
