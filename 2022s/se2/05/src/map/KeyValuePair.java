package map;

/**
 * A pair of a key of type K and a value of type V
 * @param <K> the type of the key value of this pair
 * @param <V> the type of the value value of this pair
 */
public interface KeyValuePair<K, V> {
	
	/**
	 * Gets the key value of this pair
	 * @return the key value
	 */
    K getKey();
    
    /**
     * Gets the value value of this pair
     * @return the value value
     */
    V getValue();
}
