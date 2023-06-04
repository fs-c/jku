package ssw.psw2.examtable.common;

import java.rmi.Remote;
import java.rmi.RemoteException;
import java.util.List;

public interface ExamTableModel extends Remote {
	public List<Result> getResults() throws RemoteException;

	public Result getResult(String studentID) throws RemoteException;

	public void removeResult(String result) throws RemoteException;

	public void updateResult(String result, int newPoints) throws RemoteException;

	public void addResult(String studentID, String studentName, String studentFirstName) throws RemoteException;

	public void addResultChangedListener(ResultChangedListener listener) throws RemoteException;

	public void removeResultChangedListener(ResultChangedListener listener) throws RemoteException;
}
