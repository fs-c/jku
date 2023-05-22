package ssw.psw2.examtable.backend;

import ssw.psw2.examtable.common.ExamTableModel;
import ssw.psw2.examtable.common.Result;
import ssw.psw2.examtable.common.ResultChangedListener;
import ssw.psw2.examtable.common.Student;

import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

public class ExamTableModelImpl extends UnicastRemoteObject implements ExamTableModel {
    private final DatabaseManager dbManager;
    private final List<ResultChangedListener> listeners;

    public ExamTableModelImpl() throws RemoteException {
        super();

        this.listeners = new CopyOnWriteArrayList<>();

        dbManager = new DatabaseManager();
        dbManager.openConnection(false);
        fireGeneralRefresh();
    }

    public synchronized List<Result> getResults() {
        return dbManager.importResults();
    }

    private synchronized void addResult(Result r) throws RemoteException {
        try {
            // keep db call and listener call in same catch block, so we don't fire the listener if the db op failed
            dbManager.insertResult(r);

            fireResultAdded(r);
        } catch (IllegalArgumentException e) {
            System.err.println("failed to add result");

            e.printStackTrace();
        }
    }

    @Override
    public synchronized void removeResult(String resultID) throws RemoteException {
        try {
            dbManager.removeResult(resultID);

            fireResultRemoved(resultID);
        } catch (Exception e) {
            System.err.println("failed to remove result");

            e.printStackTrace();
        }
    }

    @Override
    public synchronized void updateResult(String resultID, int newPoints) throws RemoteException {
        try {
            dbManager.updateResult(resultID, newPoints);

            fireResultChanged(resultID, newPoints);
        } catch (RuntimeException e) {
            System.err.println("failed to update result");

            e.printStackTrace();
        }
    }

    @Override
    public synchronized void addResult(String studentID, String studentName, String studentFirstName) throws RemoteException {
        addResult(new Result(new Student(studentID, studentFirstName, studentName)));
    }

    public void close() {
        dbManager.closeConnection();
    }

    @Override
    public synchronized Result getResult(String studentID) {
        return dbManager.getResult(studentID);
    }

    @Override
    public void addResultChangedListener(ResultChangedListener listener) {
        listeners.add(listener);
    }

    @Override
    public void removeResultChangedListener(ResultChangedListener listener) {
        listeners.remove(listener);
    }

    protected void fireResultAdded(Result r) throws RemoteException {
        for (ResultChangedListener l : listeners) {
            l.onResultAdded(r);
        }
    }

    protected void fireResultChanged(String resultID, int newPoints) throws RemoteException {
        for (ResultChangedListener l : listeners) {
            l.onResultChanged(resultID, newPoints);
        }
    }

    protected void fireResultRemoved(String resultID) throws RemoteException {
        for (ResultChangedListener l : listeners) {
            l.onResultRemoved(resultID);
        }
    }

    protected void fireGeneralRefresh() throws RemoteException {
        for (ResultChangedListener l : listeners) {
            l.onGeneralRefresh();
        }
    }

}
