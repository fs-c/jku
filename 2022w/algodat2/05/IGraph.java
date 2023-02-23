public interface IGraph {
    /**
     * @return Returns the number of vertices in the graph.
     */
    public int getNumberOfVertices();

    /**
     * @return Returns the number of edges in the graph.
     */
    public int getNumberOfEdges();

    /**
     * @return Returns an array of length getNumberOfVertices() with the inserted vertices
     * in their order of insertion.
     */
    public V[] getVertices();

    /**
     * @return Returns an array of length getNumberOfEdges() with the inserted edges
     * in their order of insertion.
     */
    public E[] getEdges();

    /**
     * Inserts a new vertex with the given name into the graph.
     * This methods throws an IllegalArgumentException if name is null.
     * Returns null if the graph already contains a vertex with the same name.
     * If the vertex array is already full, then the method doubleArraySize() shall
     * be called before inserting.
     * The newly added vertex should store the index at which it has been added.
     *
     * @param name the name of the vertex to be inserted
     * @return The newly added vertex, or null if vertex was already part of the graph
     * @throws IllegalArgumentException if parameter is null.
     */
    public V insertVertex(String name) throws IllegalArgumentException;

    /**
     * Returns the respective V instance for a given name, or null if no matching vertex is found.
     *
     * @param name the name of the vertex to find
     * @return the found vertex, or null if no matching vertex has been found
     * @throws IllegalArgumentException if parameter is null.
     */
    public V findVertex(String name) throws IllegalArgumentException;

    /**
     * Inserts an edge between the vertices with the names v1 and v2.
     * Returns the newly added edge.
     * null is returned if the edge already existed, or if at least one of the
     * vertices is not found in the graph.
     * An IllegalArgumentException shall be thrown if v1 or v2 is null or v1.equals(v2) (loop).
     *
     * @param v1     name of vertex 1
     * @param v2     name of vertex 2
     * @param weight weight of the edge
     * @return Returns null if the edge already exists or at least one of the vertices is not
     * part of the graph, otherwise returns the newly added edge.
     * @throws IllegalArgumentException If v1 or v2 is null or if v1 equals v2.
     */
    public E insertEdge(String v1, String v2, int weight) throws IllegalArgumentException;

    /**
     * Inserts an edge between v1 and v2.
     * Returns the newly added edge.
     * null is returned if the edge already existed, or if at least one of the
     * vertices is not part of the graph.
     * An IllegalArgumentException shall be thrown if v1 or v2 is null or v1.equals(v2) (loop).
     *
     * @param v1     vertex 1
     * @param v2     vertex 2
     * @param weight weight of the edge
     * @return Returns null if the edge already exists or at least one of the vertices is not part of the graph,
     * otherwise returns the newly added edge.
     * @throws IllegalArgumentException If v1 or v2 is null or if v1 equals v2.
     */
    public E insertEdge(V v1, V v2, int weight) throws IllegalArgumentException;

    /**
     * If there is an edge between the vertices with the name v1 and v2 returns the edge,
     * otherwise null.
     * In case of v1 or v2 being null or identical vertex names throws an IllegalArgumentException.
     *
     * @param v1 name of vertex 1
     * @param v2 name of vertex 2
     * @return Returns the edge or null if there is no edge.
     * @throws IllegalArgumentException If v1 or v2 is null or if v1 equals v2.
     */
    public E findEdge(String v1, String v2) throws IllegalArgumentException;

    /**
     * If there is an edge between the vertices with the name v1 and v2 returns the edge,
     * otherwise null.
     * In case of v1 or v2 being null or identical vertex names throws an IllegalArgumentException.
     *
     * @param v1 vertex 1
     * @param v2 vertex 2
     * @return Returns the edge or null if there is no edge.
     * @throws IllegalArgumentException If v1 or v2 is null or if v1 equals v2.
     */
    public E findEdge(V v1, V v2) throws IllegalArgumentException;

    /**
     * @return Returns an NxN adjacency matrix for the graph, where N = getNumVertices().
     * The matrix contains the edge weight if there is an edge at the corresponding index position,
     * otherwise -1.
     */
    public int[][] getAdjacencyMatrix();

    /**
     * Returns an array of vertices which are adjacent to the vertex with name v.
     *
     * @param v The name of the vertex of which adjacent vertices are searched.
     * @return array of adjacent vertices to vertex with name v, or null if the vertex is unknown
     * @throws IllegalArgumentException If v is null.
     */
    public V[] getAdjacentVertices(String v) throws IllegalArgumentException;

    /**
     * Returns an array of vertices which are adjacent to the vertex v.
     *
     * @param v The vertex of which adjacent vertices are searched.
     * @return array of adjacent vertices to vertex v, or null if vertex is unknown.
     * @throws IllegalArgumentException If v is null.
     */
    public V[] getAdjacentVertices(V v) throws IllegalArgumentException;
}
