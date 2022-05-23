package at.jku.tk.mms.voice.impl;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.lang.annotation.Target;

import javax.sound.sampled.*;
import javax.xml.transform.Source;

import at.jku.tk.mms.voice.VoiceMemo;
import at.jku.tk.mms.voice.model.Recording;

public class VoiceMemoImpl implements Runnable {
	
	private boolean playing, recording;
	
	public AudioFormat	audioFormat;
	
	private float fFrameRate = 44100.0F;
	
	private Recording lastRecording;
	
	private Recording nextToPlay;
	
	private VoiceMemo ui;
	
	public VoiceMemoImpl(VoiceMemo ui) {
		this.ui = ui;
		playing = false;
		recording = false;
		audioFormat = new AudioFormat(AudioFormat.Encoding.PCM_SIGNED, fFrameRate, 16, 2, 4, fFrameRate, false);
	}
	
	public boolean isPlaying() {
		return playing;
	}
	
	public boolean isRecoding() {
		return recording;
	}
	
	public void startRecording() {
		recording = true;
		new Thread(this).start();
	}

	public void stopRecording() {
		recording = false;
	}

	public void startPlaying() {
		playing = true;
		new Thread(this).start();
	}

	public void stopPlaying() {
		playing = false;
	}
	
	public synchronized Recording getLastRecording() {
		try {
			wait();
			return lastRecording;
		} catch (InterruptedException e) {
		}
		return null;
	}
	
	private synchronized void setLastRecording(Recording r) {
		this.lastRecording = r;
		notify();
	}
	
	public void setNextToPlay(Recording r) {
		this.nextToPlay = r;
	}

	@Override
	public void run() {
		if(playing) {
			threadPlaying();
		}
		if(recording) {
			threadRecording();
		}
	}
	
	private void threadPlaying() {
		ByteArrayInputStream stream = new ByteArrayInputStream(nextToPlay.getPcmAudio());
		// @BEGIN-ASSIGNMENT

		final DataLine.Info info = new DataLine.Info(SourceDataLine.class, audioFormat);

		SourceDataLine line;
		try {
			line = (SourceDataLine) AudioSystem.getLine(info);
			line.open();
		} catch (LineUnavailableException e) {
			throw new RuntimeException(e);
		}

		line.start();

		byte[] buffer = new byte[1024];

		while (playing) {
			final int bytesRead = stream.read(buffer, 0, buffer.length);
			line.write(buffer, 0, buffer.length);

			if (bytesRead == -1) {
				break;
			}
		}

		line.drain();
		line.stop();
		line.close();

		// @END-ASSIGNMENT
		// update the user interface with ui.updateUi();

		ui.updateUi();
	}
	
	private void threadRecording() {
		Recording r = new Recording();
		// @BEGIN-ASSIGNMENT

		final DataLine.Info info = new DataLine.Info(TargetDataLine.class, audioFormat);

		TargetDataLine line;
		try {
			line = (TargetDataLine) AudioSystem.getLine(info);
			line.open(audioFormat);
		} catch (LineUnavailableException e) {
			throw new RuntimeException(e);
		}

		line.start();

		final ByteArrayOutputStream stream = new ByteArrayOutputStream();

		byte[] buffer = new byte[64];

		while (recording) {
			final int bytesRead = line.read(buffer, 0, buffer.length);
			stream.write(buffer, 0, bytesRead);

			if (bytesRead == -1) {
				break;
			}
		}

		line.drain();
		line.stop();
		line.close();

		r.setPcmAudio(stream.toByteArray());

		setLastRecording(r);

		// @END-ASSIGNMENT
		// update the user interface with ui.updateUi();

		ui.updateUi();
	}
	
}
