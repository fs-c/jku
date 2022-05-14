package at.jku.tk.mms.voice;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JToolBar;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import at.jku.tk.mms.voice.impl.VoiceMemoImpl;
import at.jku.tk.mms.voice.impl.Waveform;
import at.jku.tk.mms.voice.model.Recording;
import at.jku.tk.mms.voice.model.RecordingListModel;

public class VoiceMemo extends JFrame implements ActionListener {

	private static final long serialVersionUID = -6388142722958826439L;
	
	private RecordingListModel list;
	private VoiceMemoImpl impl;

	private JButton record, play;
	private JList<Recording> recordings;
	
	private Waveform waveform;
	
	public VoiceMemo() {
		super("VoiceMemo");
		
		list = new RecordingListModel();
		impl = new VoiceMemoImpl(this);
		this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		initUi();
	}
	
	private void initUi() {
		setLayout(new BorderLayout());
		
		record = new JButton(new ImageIcon(getClass().getResource("/Record-Normal-icon.png")));
		record.setActionCommand("rec");
		record.addActionListener(this);
		play = new JButton(new ImageIcon(getClass().getResource("/Play-1-Hot-icon.png")));
		play.setActionCommand("play");
		play.addActionListener(this);
		JToolBar toolbar = new JToolBar();
		toolbar.add(record);
		toolbar.add(play);
		getContentPane().add(toolbar, BorderLayout.NORTH);
		
		recordings = new JList<Recording>(list);
		recordings.addListSelectionListener(new ListSelectionListener()
		  {
		    public void valueChanged(ListSelectionEvent e)
		    {
		      if (e.getValueIsAdjusting() == false)
		      {		    	
		    	Recording r = (Recording) recordings.getSelectedValue();
		    	
		    	waveform.createWaveForm(r.getPcmAudio(), impl.audioFormat);
		      }
		      
		    }


		  });
		getContentPane().add(new JScrollPane(recordings));
		
		waveform = new Waveform();
		getContentPane().add(waveform, BorderLayout.SOUTH);
		
		updateUi();
		
		pack();
	}

	public static void main(String[] args) {
		VoiceMemo m = new VoiceMemo();
		m.setVisible(true);
	}
	
	public void updateUi() {
		record.setEnabled(!impl.isPlaying());
		play.setEnabled(!impl.isRecoding());
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		String cmd = e.getActionCommand();
		if("rec".equals(cmd)) {
			if(impl.isRecoding()) {
				impl.stopRecording();
				list.addRecording(impl.getLastRecording());
			}else{
				impl.startRecording();
			}
		}
		if("play".equals(cmd)) {
			if(impl.isPlaying()) {
				impl.stopPlaying();
			}else{
				Recording r = (Recording) recordings.getSelectedValue();
				if(r != null) {
					impl.setNextToPlay(r);
					impl.startPlaying();
				}
			}
		}
		updateUi();
	}

}
