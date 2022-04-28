package map;

import list.List;

import java.util.Iterator;
import java.util.Optional;
import java.util.function.*;

/**
 * Interface for a map made of key-to-value pairs.
 *
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
     *
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
     *
     * @return An iterator that iterates over all key-value pairs in this map
     */
    Iterator<KeyValuePair<K, V>> iterator();

    /**
     * Adds a value (based on valueSupplier) for a given key k only if no entry already exists for k.
     * No value is added if key k is already present in the map - in this case, valueSupplier.get() is not executed.
     *
     * @param k             The key
     * @param valueSupplier The supplier to produce the value if no entry yet exists for key k.
     * @return true if a new entry has been added, otherwise false
     */
    boolean putIfAbsent(K k, Supplier<? extends V> valueSupplier);

    /**
     * Returns a new map that only contains those entries whose key and value return true when checked against the given predicate.
     *
     * @param predicate The predicate each entry's key and value are checked against.
     * @return A new map that contains only those entries whose key and value match the given predicate.
     */
    Map<K, V> filter(BiPredicate<? super K, ? super V> predicate);

    /**
     * Returns a new map that contains one entry for each entry in this map (i.e., the new map has the same size).
     * For each entry in this map, the new map has an entry with the same key.
     * The corresponding new value is generated using the provided newValueGenerator (by calling newValueGenerator.apply(originalKey, originalValue)).
     *
     * @param newValueGenerator A function that receives the original key and original value and returns a new value.
     * @param <NV>              The type of the values in the new map
     * @return The new map that contains the same number of entries as the original map, yet with a new value assigned to every key
     */
    <NV> Map<K, NV> mapValues(BiFunction<? super K, ? super V, ? extends NV> newValueGenerator);

    /**
     * Returns the first key-value-pair that matches the predicate (wrapped in an Optional instance), or Optional.empty()
     * if no matching key-value-pair is found
     *
     * @param predicate The predicate against which the map's key-value-pairs are checked.
     * @return The first key-value-pair that matches the predicate (wrapped in an Optional instance), or Optional.empty() if no matching key-value-pair is found
     */
    public Optional<KeyValuePair<K, V>> find(Predicate<? super KeyValuePair<K, V>> predicate);

    /**
     * Checks whether no key-value-pair in this map corresponds to the given predicate.
     *
     * @param predicate The predicate against which the map's key-value-pairs are checked.
     * @return true if no key-value-pair returns true when checked against the predicate, otherwise false.
     */
    public boolean none(Predicate<? super KeyValuePair<K, V>> predicate);

    /**
     * Checks whether all key-value-pairs in this map correspond to the given predicate.
     *
     * @param predicate The predicate against which the map's key-value-pairs are checked.
     * @return true if all key-value-pairs return true when checked against the predicate, otherwise false.
     */
    public boolean all(Predicate<? super KeyValuePair<K, V>> predicate);

    /**
     * Checks whether at least one key-value-pair in this map corresponds to the given predicate.
     *
     * @param predicate The predicate against which the map's key-value-pairs are checked.
     * @return true if at least one key-value-pair returns true when checked against the predicate, otherwise false.
     */
    public boolean some(Predicate<? super KeyValuePair<K, V>> predicate);
}
