package at.jku.tk.mms.voice.model;

import java.util.ArrayList;

import javax.swing.ListModel;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

public class RecordingListModel implements ListModel<Recording> {
	
	private ArrayList<Recording> recordings;
	
	private ArrayList<ListDataListener> listeners;
	
	public RecordingListModel() {
		recordings = new ArrayList<Recording>();
		listeners = new ArrayList<ListDataListener>();
	}

	@Override
	public Recording getElementAt(int i) {
		return recordings.get(i);
	}

	@Override
	public int getSize() {
		return recordings.size();
	}

	@Override
	public void removeListDataListener(ListDataListener l) {
		listeners.remove(l);
	}

	@Override
	public void addListDataListener(ListDataListener l) {
		listeners.add(l);
	}
	
	public void addRecording(Recording r) {
		recordings.add(r);
		ListDataEvent ev = new ListDataEvent(this, ListDataEvent.INTERVAL_ADDED, recordings.size()-1, recordings.size()-1);
		for(ListDataListener l : listeners) {
			l.intervalAdded(ev);
		}
	}

}
