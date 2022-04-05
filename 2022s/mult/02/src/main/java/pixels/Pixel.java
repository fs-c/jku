package pixels;

import java.awt.image.ColorModel;
import java.awt.image.DirectColorModel;

/** Represent a single Pixel */
public class Pixel {
	private int alpha;
	private int r, g, b;
	private int y, cb, cr;
	private int raw;

	private static final ColorModel COLOR_MODEL = ColorModel.getRGBdefault();

	/**
	 * Initialize with a raw RGB value
	 * 
	 * @param raw
	 */
	public Pixel(int raw) {
		setRaw(raw);
	}

	/**
	 * Initialize with R G B and Alpha values
	 * 
	 * @param r
	 * @param g
	 * @param b
	 * @param alpha
	 */
	public Pixel(int r, int g, int b, int alpha) {
		this.r = r;
		this.g = g;
		this.b = b;
		this.alpha = alpha;
		updateYCbCrFromRGB();
	}

	/**
	 * Initialize with YCbCr Model
	 * 
	 * @param y
	 * @param cb
	 * @param cr
	 */
	public Pixel(int y, int cb, int cr) {
		this.y = y;
		this.cb = cb;
		this.cr = cr;
		updateRGBFromYCbCr();
	}

	public static int generateRaw(int r, int g, int b, int a) {
		a = a << 24;
		r = r << 16;
		g = g << 8;
		return a | r | g | b;
	}

	public int getR() {
		return COLOR_MODEL.getRed(raw);
	}

	public int getG() {
		return COLOR_MODEL.getGreen(raw);
	}

	public int getB() {
		return COLOR_MODEL.getBlue(raw);
	}

	public int[] getRGBArray() {
		return new int[] { getR(), getG(), getB() };
	}

	private static DirectColorModel colorModel = null;

	/** Inline init of color model */
	private static DirectColorModel getColorModel() {
		if (colorModel == null) {
			colorModel = (DirectColorModel) ColorModel.getRGBdefault();
		}
		return colorModel;
	}

	/** Extract raw pixels red value */
	public static int getRed(int rgba) {
		return getColorModel().getRed(rgba);
	}

	/** Extract raw pixels green value */
	public static int getGreen(int rgba) {
		return getColorModel().getGreen(rgba);
	}

	/** Extract raw pixels blue value */
	public static int getBlue(int rgba) {
		return getColorModel().getBlue(rgba);
	}

	/** Extract raw pixels alpha channel */
	public static int getAlpha(int rgba) {
		return getColorModel().getAlpha(rgba);
	}

	/** Create single rgb values form a raw int */
	private void updateRGBFromInt() {
		r = Pixel.getRed(raw);
		g = Pixel.getGreen(raw);
		b = Pixel.getBlue(raw);
		alpha = Pixel.getAlpha(raw);
	}

	/**
	 * Generate YCbCr values from rgb
	 * 
	 * @see http://en.wikipedia.org/wiki/YCbCr and lecture slides
	 */
	private void updateYCbCrFromRGB() {
		/* @TODO Place your implementation here */
	}

	/**
	 * Genrate RGB from YCbCr values
	 * 
	 * @see http://en.wikipedia.org/wiki/YCbCr and lecture slides
	 */
	private void updateRGBFromYCbCr() {
		/* @TODO Place your implementation here */
		// we assume full alpha
		alpha = 255;
	}

	// GETTERS / SETTERS

	public int getRaw() {
		return raw;
	}

	public void setRaw(int raw) {
		this.raw = raw;
		updateRGBFromInt();
		updateYCbCrFromRGB();
	}

	public int getAlpha() {
		return alpha;
	}

	public void setAlpha(int alpha) {
		this.alpha = alpha;
		updateYCbCrFromRGB();
	}
	
	public void setR(int r) {
		this.r = r;
		updateYCbCrFromRGB();
	}

	public void setG(int g) {
		this.g = g;
		updateYCbCrFromRGB();
	}

	public void setB(int b) {
		this.b = b;
		updateYCbCrFromRGB();
	}

	public int getY() {
		return y;
	}

	public void setY(int y) {
		this.y = y;
		updateRGBFromYCbCr();
	}

	public int getCb() {
		return cb;
	}

	public void setCb(int cb) {
		this.cb = cb;
		updateRGBFromYCbCr();
	}

	public int getCr() {
		return cr;
	}

	public void setCr(int cr) {
		this.cr = cr;
		updateRGBFromYCbCr();
	}

	@Override
	public String toString() {
		StringBuilder buffer = new StringBuilder();

		buffer.append("r ");
		buffer.append(r);
		buffer.append(" g ");
		buffer.append(g);
		buffer.append(" b ");
		buffer.append(b);
		buffer.append(" a ");
		buffer.append(alpha);
		buffer.append(" y ");
		buffer.append(y);
		buffer.append(" cb ");
		buffer.append(cb);
		buffer.append(" cr ");
		buffer.append(cr);

		return buffer.toString();
	}

}
