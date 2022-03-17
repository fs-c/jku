package transport;

/**
 * Enumeration for a set of countries which are serviced by the transport company. 
 */
public enum Country {
	Austria, Germany, France, Italy, Belgium, GreatBritain, Canada, USA; 
	
	/** 
	 * Tests if the two countries are connected overland.  
	 * @param a the first country 
	 * @param b the second country 
	 * @return true if the two countries are connected overland
	 */
	public static boolean landConnected(Country a, Country b) {
		return europe(a) && europe(b) || america(a) && america(b) || a == GreatBritain && b == GreatBritain; 
	}
	
	/**
	 * Tests if the country belongs to continental Europe (not to Britain)
	 * @param e the country to be tested  
	 * @return true if the country belongs to continental Europe
	 */
	private static boolean europe(Country e) {
		return e == Austria || e == Germany || e == France || e == Italy || e == Belgium; 
	}
	
	/**
	 * Tests if the country belongs to the America continent. 
	 * @param e the country to be tested 
	 * @return true if the country belongs to the America continent
	 */
	private static boolean america(Country e) {
		return e == Canada || e == USA; 
	}
}
