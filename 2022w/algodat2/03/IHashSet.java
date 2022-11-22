public interface IHashSet {

    /**
     * returns the number of stored keys (keys must be unique!).
     */
    public int size();

    /**
     * Inserts a key and returns true if it was successful. If there is already an entry with the
     * same key, the new key will not be inserted and false is returned.
     *
     * @param key
     *        The key which shall be stored in the hash set.
     * @return
     *        True if key could be inserted, or false otherwise.
     */
    public boolean insert(int key);

    /**
     *  Searches for a given key in the hash set.
     *  @param key
     *     The key to be searched in the hash set.
     *  @return
     *     Returns true if the key is stored in the hash set, otherwise false.
     */
    public boolean contains(int key);

    /**
     * Removes the key from the hash set and returns true on success, false otherwise.
     * @param key
     *        The key to be removed from the hash set.
     * @return
     *        True if the key was found and removed, false otherwise.
     */
    public boolean remove(int key);

    /**
     * @return
     *      Returns a string representation of the hash set (array indices and stored keys) in the format
     *      Idx_0 {Node, Node, ... }, Idx_1 {...}
     *      e.g.: 0 {13}, 1 {82, 92, 12}, 2 {2, 32}, ...
     */
    public String toString();

    /**
     * Clear the hash set (setting all nodes to null resulting in a hash set of size 0).
     */
    public void clear();

    /**
     * (Required for testing only)
     * @return Return the hash table.
     */
    public ChainingHashNode[] getHashTable();

    /**
     * (Required for testing only) Set a given hash table which shall be used. Also updates the number of keys
     * stored in the hash set.
     * @param table
     *        Given hash table which shall be used.
     */
    public void setHashTable(ChainingHashNode[] table);

    /**
     * Hash function that calculates a hash code for a given key using the modulo division.
     * @param key
     *        Key for which a hash code shall be calculated according to the length of the hash table.
     * @return
     *        The calculated hash code for the given key.
     */
    public int getHashCode(int key);

}
