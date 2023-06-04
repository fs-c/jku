package ssw.psw2.examtable.frontend;

import java.io.IOException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.stage.Stage;
import ssw.psw2.examtable.backend.ExamTableModelImpl;
import ssw.psw2.examtable.common.Constants;
import ssw.psw2.examtable.common.ExamTableModel;
import javafx.scene.Parent;
import javafx.scene.Scene;

public class ExamTableGUI extends Application {
	private Controller controller;

	@Override
	public void start(Stage primaryStage) throws IOException {
		final FXMLLoader loader = new FXMLLoader(getClass().getResource("examTableUI.fxml"));
		final Parent root = loader.load();
		controller = loader.getController();

		try {
			ExamTableModel examTableModel = getModel();
			controller.postInitialize(examTableModel);
		} catch (NotBoundException e) {
			ExceptionController.displayError(e);

			// couldn't get remote model, this is fatal
			throw new RuntimeException(e);
		}

		controller.setPrimaryStage(primaryStage);

		primaryStage.setTitle("Grades");
		primaryStage.setScene(new Scene(root));
		primaryStage.show();
	}

	@Override
	public void stop() throws Exception {
		if (controller != null) {
			controller.onClose();
		}
		super.stop();
	}

	private ExamTableModel getModel() throws RemoteException, NotBoundException {
		return (ExamTableModel) LocateRegistry.getRegistry(Constants.HOST, Constants.PORT).lookup(Constants.MODEL_BINDING_NAME);
	}

	public static void main(String[] args) {
		launch(args);
	}
}