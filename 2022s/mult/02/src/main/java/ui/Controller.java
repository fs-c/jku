package ui;

import javafx.beans.property.DoubleProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleDoubleProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.embed.swing.SwingFXUtils;
import javafx.fxml.FXML;
import javafx.scene.Group;
import javafx.scene.control.*;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.*;
import javafx.stage.FileChooser;

import java.awt.image.BufferedImage;
import java.io.File;

/**
 * Controller of the JavaFX MVC Pattern
 */
public class Controller {
	private final DoubleProperty scaleFactor = new SimpleDoubleProperty(0.4);
	private final ObjectProperty<Image> currentImage = new SimpleObjectProperty<>();
	private final ObjectProperty<Image> originalImage = new SimpleObjectProperty<>();
	private final FilterScrollPane filterScrollPanel = new FilterScrollPane();
	private final FilterParameterContainer filterParameterContainer = new FilterParameterContainer();
	private final FileChooser newFileChooser = new FileChooser();
	@FXML
	private VBox rootVBox;
	@FXML
	private ImageView imageView;
	@FXML
	private BorderPane mainPane;
	@FXML
	private HBox filterBar;
	@FXML
	private Label selectedFilterName;
	@FXML
	private VBox filterParametersContainer;

	/** Initializes the UI */
	@FXML
	private void initialize() {
		initFileChoosers();
		initSplitScreen();
		initFilterBar();
		initParameterControl();
		imageView.imageProperty().bind(currentImage);
		imageView.scaleXProperty().bind(scaleFactor);
		imageView.scaleYProperty().bind(scaleFactor);
		
		filterScrollPanel.selectedFilter.addListener((obs, n, o) -> {
			if (o != null)
				runNewFilter();
		});
		filterParameterContainer.changed.addListener((o, b, a) -> runNewFilter());
		
	}

	private void initFileChoosers() {
		newFileChooser.getExtensionFilters().addAll(new FileChooser.ExtensionFilter("JPG", "*.jpg"),
				new FileChooser.ExtensionFilter("PNG", "*.png"), new FileChooser.ExtensionFilter("GIF", "*.gif"),
				new FileChooser.ExtensionFilter("BMP", "*.bmp") );

		newFileChooser.setInitialDirectory(new File(System.getProperty("user.home")));
		newFileChooser.setTitle("Choose a picture");
	}

	@FXML
	private void onNewFileClick() {
		try {
			File file = newFileChooser.showOpenDialog(rootVBox.getScene().getWindow());
			setNewImage(file);
		} catch (NullPointerException exception) {
			System.err.println("Dialog aborted!");
		}
	}

	private void initSplitScreen() {
		GridPane grid = new GridPane();

		ColumnConstraints ori = new ColumnConstraints();
		ori.setPercentWidth(50);

		ColumnConstraints filtered = new ColumnConstraints();
		filtered.setPercentWidth(50);

		RowConstraints row = new RowConstraints();
		row.setVgrow(Priority.ALWAYS);
		row.setFillHeight(true);

		grid.getColumnConstraints().addAll(ori, filtered);
		grid.getRowConstraints().addAll(row);

		grid.addColumn(0, buildImageScrollView(originalImage.getValue(), true));
		grid.addColumn(1, mainPane.getCenter());

		mainPane.setCenter(grid);
	}

	private void initFilterBar() {
		originalImage.addListener((obs, oldI, newI) -> {
			if (newI != null)
				filterBar.getChildren().setAll(filterScrollPanel.setFilterBar());
		});
	}

	private void initParameterControl() {
		filterScrollPanel.selectedFilter.addListener((obs, oldF, newF) -> {
			if (newF == null)
				return;
			filterParameterContainer.setCurrentParameters(newF.getParameters());
			selectedFilterName.setText(newF.getFilterName());
			filterParametersContainer.getChildren().setAll(filterParameterContainer.buildParameterControls());
		});
	}

	private void runNewFilter() {
		BufferedImage bImage = SwingFXUtils.fromFXImage(originalImage.getValue(), null);
		java.awt.Image filterResult = filterScrollPanel.selectedFilter.getValue()
				.runFilter(bImage, filterParameterContainer.getCurrentParameters());
				
		Image image = SwingFXUtils.toFXImage((BufferedImage)filterResult, null);
		currentImage.setValue(image);
	}

	private void setNewImage(File file) {
		filterScrollPanel.reset();
		filterParametersContainer.getChildren().clear();
		Image image = new Image(file.toURI().toString());
		originalImage.setValue(image);
		currentImage.setValue(image);
		mainPane.setCenter(buildImageScrollView(currentImage.getValue(), false));
		initSplitScreen();
	}

	private ScrollPane buildImageScrollView(Image image, boolean isStatic) {
		ImageView imgView = new ImageView(image);
		imgView.scaleXProperty().bind(scaleFactor);
		imgView.scaleYProperty().bind(scaleFactor);
		if (!isStatic) {
			imgView.imageProperty().bind(currentImage);
		}
		StackPane stackPane = new StackPane(new Group(imgView));
		stackPane.setStyle("-fx-background-color: #0F0F0F");
		
		ScrollPane scrollPane = new ScrollPane(stackPane);
		scrollPane.setStyle("-fx-background-color: #0F0F0F;");
		scrollPane.setFitToHeight(true);
		scrollPane.setFitToWidth(true);
		return scrollPane;
	}
}