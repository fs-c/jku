package inout;

import java.awt.Color;
import java.awt.Component;
import java.awt.FontMetrics;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.image.BufferedImage;


/**
 * Class allows for simple output of graphical objects on a window.
 * Provides several static methods to draw points, lines, circles and text.
 * The method {@link #clear()} will clear the window.
 */
public class Window {

    /**
     * Clears the window.
     */
    public static void clear() {
        image.getGraphics().fillRect(0, 0, DEFAULT_WIDTH, DEFAULT_HEIGHT);
        contentPane.repaint();
    }

    /**
     * Computes the width of a string.
     *
     * @param text the string
     * @return the width of the string in pixel
     */
    public static int getTextWidth(String text) {
        Graphics g = image.getGraphics();
        FontMetrics fm = g.getFontMetrics();
        return (int) Math.round(fm.getStringBounds(text, g).getWidth());
    }

   /**
    * Computes the height of text.
    *
    * @return the height of text in pixel
    */
    public static int getTextHeight() {
        Graphics g = image.getGraphics();
        FontMetrics fm = g.getFontMetrics();
        return fm.getHeight();
    }

// Methods for drawing

    /**
     * Draws a point on position x and y
     *
     * @param x the x-coordinate of the point
     * @param y the y-coordinate of the point
     */
    public static void drawPoint (int x, int y) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.fillRect(x-1, y-1, 3, 3);
        contentPane.repaint();
    }

    /**
     * Draws a line from position (x1, y1) to position (x2, y2).
     *
     * @param x1 the x-coordinate of the first point
     * @param y1 the y-coordinate of the first point
     * @param x2 the x-coordinate of the second point
     * @param y2 the y-coordinate of the second point
     */
    public static void drawLine (int x1, int y1, int x2, int y2) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawLine(x1, y1, x2, y2);
        contentPane.repaint();
    }

    /**
     * Draws a rectangle on position (x, y) with width w and height h.
     *
     * @param x the x-coordinate of the position
     * @param y the y-coordinate of the position
     * @param w the width of the rectangle
     * @param h the height of the rectangle
     */
    public static void drawRectangle (int x, int y, int w, int h) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawRect(x, y, w, h);
        contentPane.repaint();
    }

    /**
     * Draws a circle at center (x, y) and radius r.
     *
     * @param x the x-coordinate of the center
     * @param y the y-coordinate of the center
     * @param r the radius of the circle
     */
    public static void drawCircle (int x, int y, int r) {
        Graphics g = image.getGraphics();
        g.setColor(Color.black);
        g.drawOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    /**
     * Draws the text left aligned at given position
     *
     * @param text the text to draw
     * @param x the x-coordinate
     * @param y the y-coordinate
     */
    public static void drawText(String text, int x, int y) {
    	Graphics g = image.getGraphics();
    	g.setColor(Color.black);
    	g.drawString(text, x, y + getTextAscent());
        contentPane.repaint();
    }

    /**
     * Draws the text centered at given position
     *
     * @param text the text to draw
     * @param x the x-coordinate
     * @param y the y-coordinate
     */
    public static void drawTextCentered(String text, int x, int y) {
    	Graphics g = image.getGraphics();
    	g.setColor(Color.black);
    	g.drawString(text, x - getTextWidth(text)/2, y + getTextAscent());
        contentPane.repaint();
    }

    /**
     * Draws a point on position x and y with given color
     *
     * @param x the x-coordinate of the point
     * @param y the y-coordinate of the point
     */
    public static void drawPoint (int x, int y, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillRect(x-1, y-1, 3, 3);
        contentPane.repaint();
    }

    /**
     * Draws a line from position (x1, y1) to position (x2, y2) with given color.
     *
     * @param x1 the x-coordinate of the first point
     * @param y1 the y-coordinate of the first point
     * @param x2 the x-coordinate of the second point
     * @param y2 the y-coordinate of the second point
     */
    public static void drawLine (int x1, int y1, int x2, int y2, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(new Color(color.getRed(), color.getGreen(), color.getBlue()));
        g.drawLine(x1, y1, x2, y2);
        contentPane.repaint();
    }

    /**
     * Draws a rectangle on position (x, y) with width w and height h with given color.
     *
     * @param x the x-coordinate of the position
     * @param y the y-coordinate of the position
     * @param w the width of the rectangle
     * @param h the height of the rectangle
     */
    public static void drawRectangle (int x, int y, int w, int h, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.drawRect(x, y, w, h);
        contentPane.repaint();
    }

    /**
     * Draws a circle at center (x, y) and radius r with given color.
     *
     * @param x the x-coordinate of the center
     * @param y the y-coordinate of the center
     * @param r the radius of the circle
     */
    public static void drawCircle (int x, int y, int r, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(new Color(color.getRed(), color.getGreen(), color.getBlue()));
        g.drawOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    /**
     * Draws the text left aligned at given position with given color
     *
     * @param text the text to draw
     * @param x the x-coordinate
     * @param y the y-coordinate
     */
    public static void drawText(String text, int x, int y, Color color) {
    	Graphics g = image.getGraphics();
    	g.setColor(color);
    	g.drawString(text, x, y + getTextAscent());
        contentPane.repaint();
    }

    /**
     * Draws the text centered at given position
     *
     * @param text the text to draw
     * @param x the x-coordinate
     * @param y the y-coordinate
     */
    public static void drawTextCentered(String text, int x, int y, Color color) {
    	Graphics g = image.getGraphics();
    	g.setColor(color);
    	g.drawString(text, x - getTextWidth(text)/2, y + getTextAscent());
        contentPane.repaint();
    }

    /**
     * Fills a rectangle on position (x, y) with width w and height h with given color.
     *
     * @param x the x-coordinate of the position
     * @param y the y-coordinate of the position
     * @param w the width of the rectangle
     * @param h the height of the rectangle
     */
    public static void fillRectangle (int x, int y, int w, int h, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillRect(x, y, w, h);
        contentPane.repaint();
    }

    /**
     * Fills a circle at center (x, y) and radius r with given color.
     *
     * @param x the x-coordinate of the center
     * @param y the y-coordinate of the center
     * @param r the radius of the circle
     */
    public static void fillCircle (int x, int y, int r, Color color) {
        Graphics g = image.getGraphics();
        g.setColor(color);
        g.fillOval(x-r, y-r, 2*r, 2*r);
        contentPane.repaint();
    }

    /**
     * When called, waits for a mouse click in window and returns the position as result.
     * Blocks until the mouse click occurs.
     *
     * @return the point of the mouse click
     */
    public static java.awt.Point getMouseClick() {

    	final java.awt.Point p = new java.awt.Point();
    	MouseAdapter mouseAdapter = new MouseAdapter() {
    	    @Override
			public void mouseClicked(MouseEvent e) {
    	    	p.setLocation(e.getPoint());
	    		synchronized (contentPane) {
	    			contentPane.notifyAll();
	    		}
	    	}
    	};

		contentPane.addMouseListener(mouseAdapter);
    	synchronized (contentPane) {
    		try {
    			// blocks until mouse click has been done
    			contentPane.wait();
    		} catch (InterruptedException e1) {
    			e1.printStackTrace();
    		}
    	}
    	contentPane.removeMouseListener(mouseAdapter);
    	return p;
    }

// private section  --------------------------------------------------------------------------------


	/** Constant for standard width */
	private static final int DEFAULT_WIDTH = 800;

	/** Constant for height */
	private static final int DEFAULT_HEIGHT = 600;

    /** Main frame */
    private static Frame windowO;

    /** Panel for content */
    private static WindowPanel contentPane;

    /** Image object which will be used for drawing */
    private static Image image;

    /** Variable for the height of the frame */
    private static int headerHeight = 24;


    /** Inner class for closing the frame */
    private static class WindowClosingAdapter extends WindowAdapter {
        @Override
		public void windowClosing(WindowEvent event) {
            event.getWindow().setVisible(false);
            event.getWindow().dispose();
            System.exit(0);
        }
    }

    /**
     * Static inner class for the content pane of the frame.
     * Overrides the paint method and draws the image object.
     */
    @SuppressWarnings("serial")
	private static class WindowPanel extends Component {
            @Override
			public void paint(Graphics g) {
                g.drawImage(image, 0, 0, null);
            }
    }

    /**
     * Static initializer opening the window
     */
	static {
		windowO = new Frame("WindowO");
		contentPane = new WindowPanel();
		windowO.add(contentPane);
		image = new BufferedImage(DEFAULT_WIDTH, DEFAULT_HEIGHT, BufferedImage.TYPE_INT_RGB);
		image.getGraphics().fillRect(0, 0, DEFAULT_WIDTH, DEFAULT_HEIGHT);
		windowO.setSize(DEFAULT_WIDTH + 12, DEFAULT_HEIGHT + headerHeight + 12);
		windowO.addWindowListener(new WindowClosingAdapter());
		windowO.setVisible(true);
	}

    /**
     * Computes the ascent of the current font.
     * Ascent is the distance between the baseline and the top border of the text.
     *
     * @return the ascent in pixels.
     */
     private static int getTextAscent() {
         Graphics g = image.getGraphics();
         FontMetrics fm = g.getFontMetrics();
         return fm.getAscent();
     }

}
