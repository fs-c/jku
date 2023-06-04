package ssw.psw2.examtable.common;

import java.rmi.Remote;
import java.rmi.RemoteException;

public interface ResultChangedListener extends Remote {
	void onResultAdded(Result result) throws RemoteException;

	void onResultChanged(String resultID, int newPoints) throws RemoteException;

	void onResultRemoved(String resultID) throws RemoteException;

	void onGeneralRefresh() throws RemoteException;
}
