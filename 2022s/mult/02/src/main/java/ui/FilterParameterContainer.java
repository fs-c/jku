package ui;

import filters.Parameter;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

public class FilterParameterContainer {
	private List<Parameter> currentParameters;
	public BooleanProperty changed = new SimpleBooleanProperty();

	public FilterParameterContainer() {
		this.currentParameters = new ArrayList<>();
	}

	public void setCurrentParameters(List<Parameter> params) {
		currentParameters = params;
	}

	public Map<String, Parameter> getCurrentParameters() {
		return currentParameters.stream().collect(Collectors.toMap(Parameter::getName, Function.identity()));
	}

	public List<Node> buildParameterControls() {
		ArrayList<Node> controls = new ArrayList<>();

		for (Parameter p : currentParameters) {
			Label l = new Label("Please set the " + p.getName()+ ": ");
			l.setPadding(new Insets(0, 0, 16, 0));
			controls.add(l);
			Node toAdd = null;

			Slider s = new Slider(p.getMinValue(), p.getMaxValue(),p.getDefaultValue());
			s.setSnapToTicks(true);
			s.setMajorTickUnit(1);
			s.setMinorTickCount(0);
			s.setShowTickLabels(true);
			s.valueChangingProperty().addListener((obs, oldV, newV) -> {
				if (oldV && !newV) {
					p.setValue((int) s.getValue());
					changed.setValue(!changed.getValue());
				}
			});
			toAdd = s;
			controls.add(toAdd);
		}
		return controls;
	}
}
