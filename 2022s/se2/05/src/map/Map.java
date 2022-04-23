package map;

import java.util.Iterator;

/**
 * Interface for a map made of key-to-value pairs.
 * @param <K> the type for the keys 
 * @param <V> the type of the values 
 */
public interface Map<K, V> extends Iterable<KeyValuePair<K, V>> {
    /**
     * Add a value for the given key to the map.
     * If there already exists a value assigned to the given key it should be replaced.
     *
     * @param key   The key
     * @param value The value
     */
    void put(K key, V value);

    /**
     * Returns the value assigned to a given key
     *
     * @param key The key
     * @return The value assigned to the key, or null if no matching entry is found
     */
    V get(Object key);

    /**
     * Checks whether an entry exists for the given key.
     *
     * @param key The key
     * @return True if this map contains an entry for the given key, otherwise false
     */
    boolean contains(Object key);

    /**
     * Removes the entry for the given key if existing
     *
     * @param key The key
     * @return True if an entry has been removed, otherwise false
     */
    boolean remove(Object key);

    /**
     * Returns the number of entries in this map
     * @return The number of entries
     */
    int size();

    /**
     * An iterator that iterates over all keys in this map
     *
     * @return An iterator that iterates over all keys in this map
     */
    Iterator<K> keyIterator();

    /**
     * An iterator that iterates over all values in this map
     *
     * @return An iterator that iterates over all values in this map
     */
    Iterator<V> valueIterator();

    /**
     * An iterator that iterates over all key-value pairs in this map
     * @return An iterator that iterates over all key-value pairs in this map
     */
    Iterator<KeyValuePair<K, V>> iterator();
}
