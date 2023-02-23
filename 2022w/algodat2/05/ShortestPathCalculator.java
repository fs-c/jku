import java.util.ArrayList;
import java.util.HashMap;

public interface ShortestPathCalculator {
    /**
     * This method determines the shortest path between two POIs "from" and "to".
     * It returns the list of intermediate steps of the route that have been found
     * using the dijkstra algorithm.
     *
     * @param from Start vertex
     * @param to   Destination vertex
     * @return
     * 	The path, with all intermediate steps, returned as an ArrayList. This list
     * 	sequentially contains each vertex along the shortest path, together with
     * 	the already covered distance (see example on the assignment sheet).
     * 	Returns null if there is no path between the two given vertices.
     * @throws IllegalArgumentException
     *   If from or to is null, or if from equals to
     */
    public ArrayList<Step> getShortestPathFromTo(V from, V to) throws IllegalArgumentException;

    /**
     * This method determines the shortest paths from a given "from" vertex to all other vertices.
     * The shortest distance (or -1 if no path exists) to each vertex is returned
     * as a hash map, using the vertex name as key and the distance as value.
     *
     * @param from Start vertex
     * @return
     *   A map containing the shortest distance (or -1 if no path exists) to each vertex,
     *   using the vertex name as key and the distance as value.
     * @throws IllegalArgumentException
     *   If from is null.
     */
    public HashMap<String, Integer> getShortestDistancesFrom(V from) throws IllegalArgumentException;

    /**
     * This method determines the amount of "steps" needed on the shortest paths
     * from a given "from" vertex to all other vertices.
     * The number of steps (or -1 if no path exists) to each vertex is returned
     * as a hash map, using the vertex name as key and the number of steps as value.
     * E.g., the "from" vertex has a step count of 0 to itself and 1 to all adjacent vertices.
     *
     * @param from Start vertex
     * @return
     *   A map containing the number of steps (or -1 if no path exists) on the
     *   shortest path to each vertex, using the vertex name as key and the number of steps as value.
     * @throws IllegalArgumentException
     *   If from is null.
     */
    public HashMap<String, Integer> getStepsForShortestPathsFrom(V from) throws IllegalArgumentException;
}
