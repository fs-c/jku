import java.util.Arrays;
import java.util.Objects;

public class G implements IGraph {
    /**
     * Vertex array
     * (public for testing purpose only)
     */
    public V vertices[];
    /**
     * Edge array
     * (public for testing purpose only)
     */
    public E edges[];

    private int numVertices;
    private int numEdges;

    // Creates an empty graph.
    public G() {
        vertices = new V[1];
        edges = new E[1];

        numVertices = 0;
        numEdges = 0;
    }

    private void doubleVertexArraySize() {
        vertices = Arrays.copyOf(vertices, vertices.length * 2);
    }

    private void doubleEdgeArraySize() {
        edges = Arrays.copyOf(edges, edges.length * 2);
    }

    public int getNumberOfVertices() {
        return numVertices;
    }

    public int getNumberOfEdges() {
        return numEdges;
    }

    public V[] getVertices() {
        return Arrays.copyOf(vertices, numVertices);
    }

    public E[] getEdges() {
        return Arrays.copyOf(edges, numEdges);
    }

    public V insertVertex(String name) throws IllegalArgumentException {
        if (name == null) {
            throw new IllegalArgumentException("Vertex name cannot be null");
        }

        if (findVertex(name) != null) {
            return null;
        }

        if (numVertices >= vertices.length) {
            doubleVertexArraySize();
        }

        var v = new V(numVertices, name);

        vertices[numVertices++] = v;

        return v;
    }

    public V findVertex(String name) throws IllegalArgumentException {
        if (name == null) {
            throw new IllegalArgumentException("Vertex name cannot be null");
        }

        for (var v : vertices) {
            if (v != null && v.name.equals(name)) {
                return v;
            }
        }

        return null;
    }

    public E insertEdge(String v1, String v2, int weight) throws IllegalArgumentException {
        if (v1 == null || v2 == null) {
            throw new IllegalArgumentException("Vertex names cannot be null");
        } else if (v1.equals(v2)) {
            throw new IllegalArgumentException("Cannot create a loop");
        }

        var vertex1 = findVertex(v1);
        var vertex2 = findVertex(v2);

        if (vertex1 == null || vertex2 == null) {
            return null;
        }

        return insertEdge(vertex1, vertex2, weight);
    }

    public E insertEdge(V v1, V v2, int weight) throws IllegalArgumentException {
        if (v1 == null || v2 == null) {
            throw new IllegalArgumentException("Vertices cannot be null");
        } else if (v1.equals(v2)) {
            throw new IllegalArgumentException("Cannot create a loop");
        }

        if (findEdge(v1, v2) != null) {
            return null;
        }

        if (numEdges >= edges.length) {
            doubleEdgeArraySize();
        }

        var e = new E(v1, v2, weight);

        edges[numEdges++] = e;

        return e;
    }

    public E findEdge(String v1, String v2) throws IllegalArgumentException {
        if (v1 == null || v2 == null) {
            throw new IllegalArgumentException("Vertex names cannot be null");
        } else if (v1.equals(v2)) {
            throw new IllegalArgumentException("There cannot be an edge between a vertex and itself");
        }

        for (var e : edges) {
            if (e == null) {
                continue;
            }

            boolean first = e.first.name.equals(v1) && e.second.name.equals(v2);
            boolean second = e.first.name.equals(v2) && e.second.name.equals(v1);

            if (first || second) {
                return e;
            }
        }

        return null;
    }

    public E findEdge(V v1, V v2) throws IllegalArgumentException {
        if (v1 == null || v2 == null) {
            throw new IllegalArgumentException("Vertices cannot be null");
        }

        return findEdge(v1.name, v2.name);
    }

    public int[][] getAdjacencyMatrix() {
        var matrix = new int[numVertices][numVertices];

        for (int i = 0; i < numVertices; i++) {
            for (int j = 0; j < numVertices; j++) {
                try {
                    var edge = findEdge(vertices[i], vertices[j]);

                    if (edge != null) {
                        matrix[i][j] = edge.weight;
                    } else {
                        matrix[i][j] = -1;
                    }
                } catch (IllegalArgumentException e) {
                    matrix[i][j] = -1;
                }
            }
        }

        return matrix;
    }

    public V[] getAdjacentVertices(String name) throws IllegalArgumentException {
        if (name == null) {
            throw new IllegalArgumentException("Vertex name cannot be null");
        } else if (findVertex(name) == null) {
            return null;
        }

        int adjacentIndex = 0;
        var adjacent = new V[numVertices];

        for (var e : edges) {
            if (e == null) {
                continue;
            } else if (e.first.name.equals(name)) {
                adjacent[adjacentIndex++] = e.second;
            } else if (e.second.name.equals(name)) {
                adjacent[adjacentIndex++] = e.first;
            }
        }

        return Arrays.copyOf(adjacent, adjacentIndex);
    }

    public V[] getAdjacentVertices(V v) throws IllegalArgumentException {
        if (v == null) {
            throw new IllegalArgumentException("Vertex cannot be null");
        }

        return getAdjacentVertices(v.name);
    }
}
