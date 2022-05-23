package at.jku.tk.mms.voice.impl;

import javax.sound.sampled.AudioFormat;
import javax.swing.JPanel;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.geom.Line2D;
import java.awt.geom.Line2D.Double;
import java.util.Vector;

public class Waveform extends JPanel {

	Vector<Double> lines = new Vector<Double>();
	
    Color jfcBlue = new Color(204, 204, 255);
    Color pink = new Color(255, 175, 175);

    public Waveform() {
        setBackground(new Color(20, 20, 20));
        setPreferredSize(new Dimension(500,100));
    }


    public void createWaveForm(byte[] audioBytes, AudioFormat format) {
		// @BEGIN-ASSIGNMENT



		// @END-ASSIGNMENT

        repaint();
    }
    
    
    public void paint(Graphics g) {

        Dimension d = getSize();
        int w = d.width;
        int h = d.height;
        int INFOPAD = 15;

        Graphics2D g2 = (Graphics2D) g;
        g2.setBackground(getBackground());
        g2.clearRect(0, 0, w, h);
        g2.setColor(Color.white);
        g2.fillRect(0, h-INFOPAD, w, INFOPAD);

		// @BEGIN-ASSIGNMENT

		// @END-ASSIGNMENT
		
    }

} // End class Waveform


