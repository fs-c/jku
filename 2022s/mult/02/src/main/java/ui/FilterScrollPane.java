package ui;

import filters.*;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.ListView;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class FilterScrollPane {
	public final ObjectProperty<Filter> selectedFilter = new SimpleObjectProperty<>();
	private final List<Filter> filters;

	public FilterScrollPane() {
		// registering all filters
		this.filters = Arrays.asList(new ThresholdFilter(), new GrayScaleFilter(), new SepiaFilter(), new Subsampling());

	}

	public List<Node> setFilterBar() {
		List<Node> nodes = new ArrayList<>();

		for (Filter filter : filters) {
			StackPane stackPane = new StackPane();
			ListView<Button> list = new ListView<Button>();
			list.setPrefHeight(50);
			list.setPrefWidth(120);
			list.setStyle("-fx-background-color: #929292;");
			list.setOrientation(Orientation.HORIZONTAL);

			Button bFilter = new Button(filter.getFilterName());
			bFilter.setUserData(filter);
			bFilter.setOnMouseClicked(
					event -> selectedFilter.setValue((Filter) ((Button) event.getSource()).getUserData()));

			stackPane.getChildren().addAll(list, bFilter);
			stackPane.setUserData(filter);
			stackPane.setStyle("-fx-background-color: #929292; ");
			stackPane.setOnMouseClicked(
					event -> selectedFilter.setValue((Filter) ((StackPane) event.getSource()).getUserData()));

			VBox vbButtons = new VBox();
			vbButtons.setSpacing(10);
			vbButtons.setPadding(new Insets(0, 20, 10, 20));
			vbButtons.getChildren().addAll(bFilter);

			nodes.add(bFilter);
		}

		return nodes;
	}

	public void reset() {
		selectedFilter.setValue(null);
	}
}
