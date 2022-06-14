package inout;

import java.awt.Color;
import java.awt.Component;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.image.BufferedImage;


/**
 * Diese Klasse erlaubt die einfache Ausgabe von graphischen Objekten Punkt, Linie, Kreis und
 * Rechteck in einem statischen Fenster. Dazu stellt es eine Reihe von statischen Methoden zur Verfügung:
 *
 * Mit Methode open wird die Klasse initialisiert und ein Fenster erzeugt und geöffnet.
 * <p>
 * Methoden drawPoint, drawLine, drawCircle und drawRectangle erlauben das Zeichnen von Punkten,
 * Strecken, Kreisen bzw. Rechtecken. Weiters gibt es die Methoden mit einem zusätzlichen Parameter
 * color, mit der die Farbe zum Zeichnen spezifiziert werden kann.
 * <p>
 * Methoden fillCircle und fillRectangle erlauben das Zeichnen von Kreisen bzw. Rechtecken
 * gefüllt mit einer bestimmten Farbe.
 * <p>
 * Die Klasse hat eine Reihe von Restriktionen, die beachtet werden sollten.
 * Das Fenster hat eine fixe Größe (standardmäßig 800 mal 600 Pixel) und erlaubt kein Scrollen.
 * Das Fenster sollte auch nicht vergrößert werden.
 *
 * @author Herbert Praehofer
 * @date
 */
public class Window {

// Breite und Höhe

	/** Konstante für Standardbreite */
	public static final int DEFAULT_WIDTH = 800;

	/** Konstante für Standardhöhe */
	public static final int DEFAULT_HEIGHT = 600;

    /** Variable, welche die Breite des Fensters definiert. */
    public static int width;

    /** Variable, welche die Hoehe des Fensters definiert. */
    public static int height;

// open

    /**
     * Initialisiert das Ausgabefenster und öffnet es.
     */
    public static void open() {
        open(DEFAULT_WIDTH, DEFAULT_HEIGHT);
    }

   /**
     * Initialisiert das Ausgabefenster und öffnet es.
     * @param w Die Breite für das
     * @param w Die Hoehe für das Fenster
     */
    public static void open(int w, int h) {
    	width = w;
    	height = h;
        windowO = new Frame("WindowO");
        contentPane = new WindowOPanel();
        windowO.add(contentPane);
        image = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
        image.getGraphics().fillRect(0, 0, w, h);
        windowO.setSize(w + 12, h + headerHeight + 12);
        windowO.addWindowListener(new Window.WindowClosingAdapter(true));
        windowO.setVisible(true);
    }

    /** Löscht den Inhalt des Fensters */
    public static void clear() {
        image.getGraphics().fillRect(0, 0, width, height);
        contentPane.repaint();
    }

// Methoden zum Zeichnen.

    /** Zeichnet einen Punkt bei der angebenen Position (x, y). */
    public static void drawPoint (int x, int y) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.fillRect(x-1, y-1, 3, 3);
        contentPane.repaint();
    }

    /** Zeichnet eine Linie von Position (x1, y1) zu Position (x2, y2). */
    public static void drawLine (int x1, int y1, int x2, int y2) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawLine(x1, y1, x2, y2);
        contentPane.repaint();
    }

    /** Zeichnet ein Rechteck bei Position (x, y) mit Breite w und Höhe h. */
    public static void drawRectangle (int x, int y, int w, int h) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawRect(x, y, w, h);
        contentPane.repaint();
    }

    /** Zeichnet einen Kreis mit Mittelpunkt (x, y) und Radius r. */
    public static void drawCircle (int x, int y, int r) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    /** Gibt den Text text auf Position x/y aus */
    public static void drawText(String text,int x, int y) {
    	Graphics g = image.getGraphics();
    	g.setColor(Color.black);
    	g.drawString(text, x, y);
        contentPane.repaint();
    }

    /** Zeichnet einen Punkt bei der angebenen Position (x, y) mit Farbe color. */
    public static void drawPoint (int x, int y, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillRect(x-1, y-1, 3, 3);
        contentPane.repaint();
    }

    /** Zeichnet eine Linie von Position (x1, y1) zu Position (x2, y2) mit Farbe color. */
    public static void drawLine (int x1, int y1, int x2, int y2, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(new Color(color.getRed(), color.getGreen(), color.getBlue()));
        g.drawLine(x1, y1, x2, y2);
        contentPane.repaint();
    }

    /** Zeichnet ein Rechteck bei Position (x, y) mit Breite w und Höhe h mit Farbe color. */
    public static void drawRectangle (int x, int y, int w, int h, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.drawRect(x, y, w, h);
        contentPane.repaint();
    }

    /** Zeichnet einen Kreis Zeichnet einen Kreis mit Mittelpunkt (x, y) und Radius r mit Farbe color. */
    public static void drawCircle (int x, int y, int r, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(new Color(color.getRed(), color.getGreen(), color.getBlue()));
        g.drawOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    /** Gibt den Text text auf Position x/y in Farbe color aus */
    public static void drawText(String text,int x, int y, Color color) {
    	Graphics g = image.getGraphics();
    	g.setColor(color);
    	g.drawString(text, x, y);
        contentPane.repaint();
    }

    /** Zeichnet ein gefülltes Rechteck bei Position (x, y) mit Breite w und Höhe h mit Farbe color. */
    public static void fillRectangle (int x, int y, int w, int h, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillRect(x, y, w, h);
        contentPane.repaint();
    }

    /** Zeichnet einen gefüllten Kreis mit Mittelpunkt (x, y) und Radius r mit Farbe color. */
    public static void fillCircle (int x, int y, int r, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    private static java.awt.Point p = null;

    /**
     * Wartet auf einen Mouseclick im Fenster und liefert die Position als Ergebnis.
     * Blockiert solange der Mouseclick nicht erfolgt ist.
     * @return die Position des Mouseclicks
     */
    public static java.awt.Point getMouseClick() {

    	contentPane.addMouseListener(new MouseAdapter() {
    	    /**
    	     * Invoked when the mouse has been clicked on a component.
    	     */
    	    @Override
			public void mouseClicked(MouseEvent e) {
    	    	p = e.getPoint();
	    		synchronized (contentPane) {
	    			contentPane.notifyAll();
	    		}
	    	}
    	});

    	// blockiere solange Mouseclick nicht erfolgte
    	synchronized (contentPane) {
    		try {
    			contentPane.wait();
    		} catch (InterruptedException e1) {
    			e1.printStackTrace();
    		}
    	}
    	return p;
    }

// Privater Bereich --------------------------------------------------------------------------------

    /** Main-Frame */
    private static Frame windowO;

    /** Panel mit Inhalt. Ist von Klasse WindowOPanel, welches das BufferedImage image zeichnet*/
    private static WindowOPanel contentPane;

    /** BufferedImage, in welches gezeichnet wird und welches dann in contentPane ausgegeben wird */
    private static Image image;

    /** Variable, die die Hoehe des Headers des Frame definiert */
    private static int headerHeight = 24;


    /** Innere Klasse zum Schließen des Frame */
    static class WindowClosingAdapter extends WindowAdapter {

        private boolean exitSystem;

        /**
        * Erzeugt einen WindowClosingAdapter zum Schliessen
        * des Fensters. Ist exitSystem true, wird das komplette
        * Programm beendet.
        */
        public WindowClosingAdapter(boolean exitSystem) {
            this.exitSystem = exitSystem;
        }

        /**
        * Erzeugt einen WindowClosingAdapter zum Schliessen
        * des Fensters. Das Programm wird nicht beendet.
        */
        public WindowClosingAdapter() {
             this(true);
        }

        /** Schließt das Fenster  und terminiert die Anwendung */
        @Override
		public void windowClosing(WindowEvent event) {
            event.getWindow().setVisible(false);
            event.getWindow().dispose();
            if (exitSystem) {
                System.exit(0);
            }
        }
    }

    /**
     * Klasse für die contentPane im WindowO Frame.
     * Es wird paint von Component überschrieben und das BufferedImage image gezeichnet.
     */
    static class WindowOPanel extends Component {
            @Override
			public void paint(Graphics g) {
                g.drawImage(image, 0, 0, null);
            }
    }
}
