package at.jku.tk.mms.voice.model;

import java.util.Date;

public class Recording {

	private String name;
	
	private byte[] pcmAudio;
	
	public Recording() {
		name = new Date().toString();
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	public byte[] getPcmAudio() {
		return pcmAudio;
	}
	
	public void setPcmAudio(byte[] pcmAudio) {
		this.pcmAudio = pcmAudio;
	}

	@Override
	public String toString() {
		return name;
	}
	
}
