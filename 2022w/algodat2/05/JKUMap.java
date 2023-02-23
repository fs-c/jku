import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class JKUMap extends G implements ShortestPathCalculator {
    public JKUMap() {
        V spar = insertVertex("Spar");
        V lit = insertVertex("LIT");
        V openLab = insertVertex("Open Lab");
        V porter = insertVertex("Porter");
        V khg = insertVertex("KHG");
        V bank = insertVertex("Bank");
        V chat = insertVertex("Chat");
        V parking = insertVertex("Parking");
        V teichwerk = insertVertex("Teichwerk");
        V library = insertVertex("Library");
        V bellaCasa = insertVertex("Bella Casa");
        V lui = insertVertex("LUI");
        V castle = insertVertex("Castle");
        V sp1 = insertVertex("SP1");
        V papaya = insertVertex("Papaya");
        V sp3 = insertVertex("SP3");
        V jkh = insertVertex("JKH");

        insertEdge(spar, lit, 50);
		insertEdge(spar, porter, 103);
        insertEdge(spar, khg, 165);
        insertEdge(lit, porter, 80);
        insertEdge(openLab, porter, 70);
        insertEdge(porter, bank, 100);
        insertEdge(khg, bank, 150);
        insertEdge(khg, parking, 190);
        insertEdge(bank, chat, 115);
        insertEdge(chat, library, 160);
        insertEdge(chat, lui, 240);
        insertEdge(parking, bellaCasa, 145);
        insertEdge(parking, sp1, 240);
        insertEdge(teichwerk, lui, 135);
        insertEdge(library, lui, 90);
        insertEdge(lui, sp1, 175);
        insertEdge(castle, papaya, 85);
        insertEdge(sp1, sp3, 130);
        insertEdge(papaya, jkh, 80);
    }

    private HashMap<V, Integer> getInitialDistances(V initial) {
        HashMap<V, Integer> distances = new HashMap<V, Integer>();

        for (V v : getVertices()) {
            distances.put(v, Integer.MAX_VALUE);
        }

        distances.put(initial, 0);
        return distances;
    }

    private HashMap<V, ArrayList<V>> getInitialPaths(V initial) {
        var initialPath = new ArrayList<V>();
        initialPath.add(initial);

        var paths = new HashMap<V, ArrayList<V>>();
        paths.put(initial, initialPath);

        return paths;
    }

    @Override
    public ArrayList<Step> getShortestPathFromTo(V from, V to) throws IllegalArgumentException {
        if (from == null || to == null || from == to) {
            throw new IllegalArgumentException("From and to must not be null or equal");
        }

        var visited = new HashSet<V>();
        var distances = getInitialDistances(from);
        var paths = getInitialPaths(from);

        dijkstra(from, visited, distances, paths);

        var path = paths.get(to);

        if (path == null) {
            return null;
        }

        var shortestPath = new ArrayList<Step>();

        for (V v : path) {
            shortestPath.add(new Step(v, distances.get(v)));
        }

        return shortestPath;
    }

    @Override
    public HashMap<String, Integer> getStepsForShortestPathsFrom(V from) {
        if (from == null) {
            throw new IllegalArgumentException("From must not be null");
        }

        var visited = new HashSet<V>();
        var distances = getInitialDistances(from);
        var paths = getInitialPaths(from);

        dijkstra(from, visited, distances, paths);

        var steps = new HashMap<String, Integer>();

        for (V v : getVertices()) {
            var path = paths.get(v);

            steps.put(v.name, path == null ? -1 : (path.size() - 1));
        }

        return steps;
    }

    @Override
    public HashMap<String, Integer> getShortestDistancesFrom(V from) {
        if (from == null) {
            throw new IllegalArgumentException("From must not be null");
        }

        var visited = new HashSet<V>();
        var distances = getInitialDistances(from);
        var paths = getInitialPaths(from);

        dijkstra(from, visited, distances, paths);

        var shortestDistances = new HashMap<String, Integer>();
        distances.forEach((k, v) -> {
            if (v == Integer.MAX_VALUE) {
                shortestDistances.put(k.name, -1);
            }  else {
                shortestDistances.put(k.name, v);
            }
        });

        return shortestDistances;
    }

    /**
     * This method is expected to be called with correctly initialized data structures and recursively calls itself.
     *
     * @param cur Current vertex being processed
     * @param visited Set which notes already visited vertices.
     * @param distances Map (nVertices entries) which stores the min. distance to each vertex.
     * @param paths Map (nVertices entries) which stores the shortest path to each vertex .
     */
    private void dijkstra(V cur, HashSet<V> visited, HashMap<V, Integer> distances, HashMap<V, ArrayList<V>> paths) {
        visited.add(cur);

        for (var neighbor : getAdjacentVertices(cur)) {
            if (visited.contains(neighbor)) {
                continue;
            }

            int edgeWeight = findEdge(cur, neighbor).weight;
            int distance = distances.get(cur) + edgeWeight;

            if (distance < distances.get(neighbor)) {
                distances.put(neighbor, distance);

                var path = new ArrayList<>(paths.get(cur));
                path.add(neighbor);
                paths.put(neighbor, path);
            }
        }

        V next = null;
        int minDistance = Integer.MAX_VALUE;

        for (V v : getVertices()) {
            if (visited.contains(v)) {
                continue;
            }

            int distance = distances.get(v);

            if (distance < minDistance) {
                next = v;
                minDistance = distance;
            }
        }

        if (next != null) {
            dijkstra(next, visited, distances, paths);
        }
    }
}
