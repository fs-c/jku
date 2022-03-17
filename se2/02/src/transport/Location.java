package transport;

/**
 * Represents a location that can be reached by a transporter. As a
 * simplification, a location is specified via its x-coordinate and y-coordinate
 * and the country.<br>
 * A location object is immutable, i.e. it is not possible to change the data
 * fields after the construction of the object.
 */
public class Location {
	/** Name of the location. */
	private final String name;
	/** x-coordinate of the location. */
	private final int xCoord;
	/** y-coordinate of the location. */
	private final int yCoord;
	/** the country of this location. */
	private final Country country;

	/**
	 * Creates a new location and initializes all fields.
	 * 
	 * @param name
	 *            The name of the location.
	 * @param xCoord
	 *            The x-coordinate of the location.
	 * @param yCoord
	 *            The y-coordinate of the location.
	 * @param country
	 *            The country of this location.
	 */
	public Location(String name, int xCoord, int yCoord, Country country) {
		super();
		this.name = name;
		this.xCoord = xCoord;
		this.yCoord = yCoord;
		this.country = country;
	}

	/**
	 * Checks if this location is in the same country as the
	 * <code>other</code> location.
	 * 
	 * @param other
	 *            The other location.
	 * @return true if the country name is equal, false otherwise.
	 */
	public boolean reachableOverland(Location other) {
		return Country.landConnected(this.country, other.country);
	}

	/**
	 * Computes the distance between this location and the <code>other</code>
	 * location.
	 * 
	 * @param other
	 *            The other location.
	 * @return the distance between the locations.
	 */
	public double getDistance(Location other) {
		double dx = xCoord - other.xCoord;
		double dy = yCoord - other.yCoord;
		return Math.sqrt(dx * dx + dy * dy);
	}

	/**
	 * Returns the name of the location.
	 * 
	 * @return The name.
	 */
	public String getName() {
		return name;
	}

	/**
	 * Returns the country name of the location.
	 * 
	 * @return The country name.
	 */
	public Country getCountry() {
		return country;
	}

	@Override
	public String toString() {
		return String.format("%1$s in %2$s at (%3$d/%4$d)", name, country, xCoord, yCoord);
	}
}
