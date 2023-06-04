package ssw.psw2.examtable.backend;

import ssw.psw2.examtable.common.Constants;
import ssw.psw2.examtable.common.ExamTableModel;

import java.rmi.AlreadyBoundException;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;

public class ExamTableServer {
    public static void main(String[] args) {
        try {
            final ExamTableModel model = new ExamTableModelImpl();
            final Registry reg = LocateRegistry.createRegistry(Constants.PORT);

            reg.bind(Constants.MODEL_BINDING_NAME, model);

            System.out.format("registry listening on port %d, exposing '%s'\n", Constants.PORT, Constants.MODEL_BINDING_NAME);
        } catch (RemoteException e) {
            System.err.format("generic remote exception: %s\n", e.getMessage());

            e.printStackTrace();
        } catch (AlreadyBoundException e) {
            System.err.format("couldn't bind to '%s', already bound\n", Constants.MODEL_BINDING_NAME);

            e.printStackTrace();
        }
    }
}
