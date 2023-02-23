import org.junit.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Timeout;

import java.util.Arrays;
import java.util.HashSet;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

public class Assignment06TestStudent {

    public FordFulkerson network;

    // https://en.wikipedia.org/wiki/Edmonds%E2%80%93Karp_algorithm
    private int[][] _wikigraph = {
            {0, 3, 0, 3, 0, 0, 0},
            {0, 0, 4, 0, 0, 0, 0},
            {3, 0, 0, 1, 2, 0, 0},
            {0, 0, 0, 0, 2, 6, 0},
            {0, 1, 0, 0, 0, 0, 1},
            {0, 0, 0, 0, 0, 0, 9},
            {0, 0, 0, 0, 0, 0, 0}
    };
    private int[][] _maxWikiFlow = {
            {0, 2, 0, 3, 0, 0, 0},
            {0, 0, 2, 0, 0, 0, 0},
            {0, 0, 0, 1, 1, 0, 0},
            {0, 0, 0, 0, 0, 4, 0},
            {0, 0, 0, 0, 0, 0, 1},
            {0, 0, 0, 0, 0, 0, 4},
            {0, 0, 0, 0, 0, 0, 0}
    };

    private int[][] _graph1 = {
            {0, 8, 0, 0, 3, 0},
            {0, 0, 9, 0, 0, 0},
            {0, 0, 0, 0, 7, 4},
            {0, 0, 0, 0, 0, 5},
            {0, 0, 0, 4, 0, 0},
            {0, 0, 0, 0, 0, 0}
    };

    private int[][] _graph2 = {
            {0, 67, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 99, 64, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 84, 0, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 19, 16, 89, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 86, 77, 0, 77, 0, 0, 68},
            {93, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 9, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 17, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 9},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 32, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 98, 0, 83, 0, 0, 6, 94, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 82, 84},
            {0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 95, 0, 0, 0, 0}
    };

    private int[][] _graph3 = {
            {0, 16, 13, 0, 0, 0},
            {0, 10, 0, 12, 0, 0},
            {0, 4, 0, 0, 14, 0},
            {0, 0, 9, 0, 0, 20},
            {0, 0, 0, 7, 0, 4},
            {0, 0, 0, 0, 0, 0}};

    private int[][] _graph4 = {
            {0, 16, 13, 0, 0, 0},
            {0, 0, 10, 12, 0, 0},
            {0, 0, 0, 0, 14, 0},
            {0, 0, 9, 0, 0, 20},
            {0, 0, 0, 7, 0, 4},
            {0, 0, 0, 0, 0, 0}
    };

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkersonWiki() {
        network = new FlowNetwork(_wikigraph);
        int source = 0;
        int sink = 6;
        int flow = network.execute(source, sink);

        assertEquals(5, flow, "max flow should be 5");

        assertTrue(networkIsSmallerThan(network.getCurrentFlow(), network.getGraph()),
                "Max flow must be smaller than capacities.\n" +
                        "Flow:  " + Arrays.deepToString(network.getCurrentFlow()) + "\n" +
                        "Graph: " + Arrays.deepToString(network.getGraph()));

        for (int node = 0; node < _maxWikiFlow.length; node++) {
            assertArrayEquals(network.getCurrentFlow()[node], _maxWikiFlow[node], String.format("Flow of node %d incorrect", node));
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkerson1() {
        network = new FlowNetwork(_graph1);
        int source = 0;
        int sink = 5;
        int flow = network.execute(source, sink);

        assertEquals(8, flow, "max flow should be 8");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkersonStep1() {
        network = new FlowNetwork(_graph1);
        int source = 0;
        int sink = 5;
        int flow = 0;

        int[][] residualGraph = cloneGraph(_graph1);

        int pathFlow = network.step(source, sink);
        while (pathFlow > 0) {
            flow += pathFlow;

            // retrieve unique content
            HashSet<Integer> uniques = getUniques(network.getLatestAugmentingPath());
            assertEquals(2, uniques.size(),
                    "Latest augmenting path should have 2 values\n\n\t");

            assertTrue(networkIsSmallerThan(network.getCurrentFlow(), network.getGraph()),
                    "Current flow must be smaller than capacities.\n" +
                            "Flow:  " + Arrays.deepToString(network.getCurrentFlow()) + "\n" +
                            "Graph: " + Arrays.deepToString(network.getGraph()));

            assertTrue(networkIsSmallerThan(network.getLatestAugmentingPath(), residualGraph),
                    "Latest path must be smaller than residual graph.\n" +
                            "Path:  " + Arrays.deepToString(network.getLatestAugmentingPath()) + "\n" +
                            "Graph: " + Arrays.deepToString(residualGraph));

            residualGraph = cloneGraph(network.getCurrentResidualGraph());
            pathFlow = network.step(source, sink);
        }
        assertEquals(8, flow, "max flow should be 8 : " + flow + " given \n\n\t");

    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkerson2() {
        network = new FlowNetwork(_graph2);
        int source = 0;
        int sink = 15;
        int flow = network.execute(source, sink);

        assertEquals(41, flow, "max flow should be 41 : " + flow + " given \n\n\t");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkersonStep2() {

        network = new FlowNetwork(_graph2);
        int source = 0;
        int sink = 15;
        int flow = 0;
        int[][] residualGraph = cloneGraph(_graph2);

        int pathFlow = network.step(source, sink);
        while (pathFlow > 0) {
            flow += pathFlow;

            // retrieve unique content
            HashSet<Integer> uniques = getUniques(network.getLatestAugmentingPath());
            assertEquals(2, uniques.size(),
                    "Latest augmenting path should have 2 values \n\n\t");

            assertTrue(networkIsSmallerThan(network.getCurrentFlow(), network.getGraph()),
                    "Current flow must be smaller than capacities.\n" +
                            "Flow:  " + Arrays.deepToString(network.getCurrentFlow()) + "\n" +
                            "Graph: " + Arrays.deepToString(network.getGraph()));

            assertTrue(networkIsSmallerThan(network.getLatestAugmentingPath(), residualGraph),
                    "Latest path must be smaller than residual graph.\n" +
                            "Path:  " + Arrays.deepToString(network.getLatestAugmentingPath()) + "\n" +
                            "Graph: " + Arrays.deepToString(residualGraph));

            residualGraph = cloneGraph(network.getCurrentResidualGraph());
            pathFlow = network.step(source, sink);
        }
        assertEquals(41, flow, "max flow should be 41 : " + flow + " given \n\n\t");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkerson3() {
        network = new FlowNetwork(_graph3);
        int source = 0;
        int sink = 5;
        int flow = network.execute(source, sink);

        assertEquals(23, flow, "max flow should be 23 : " + flow + " given \n\n\t");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkersonStep3() {

        network = new FlowNetwork(_graph3);
        int source = 0;
        int sink = 5;
        int flow = 0;
        int[][] residualGraph = cloneGraph(_graph3);

        int pathFlow = network.step(source, sink);
        while (pathFlow > 0) {
            flow += pathFlow;

            // retrieve unique content
            HashSet<Integer> uniques = getUniques(network.getLatestAugmentingPath());
            assertEquals(2, uniques.size(),
                    "Latest augmenting path should have 2 values \n\n\t");

            assertTrue(networkIsSmallerThan(network.getCurrentFlow(), network.getGraph()),
                    "Current flow must be smaller than capacities.\n" +
                            "Flow:  " + Arrays.deepToString(network.getCurrentFlow()) + "\n" +
                            "Graph: " + Arrays.deepToString(network.getGraph()));

            assertTrue(networkIsSmallerThan(network.getLatestAugmentingPath(), residualGraph),
                    "Latest path must be smaller than residual graph.\n" +
                            "Path:  " + Arrays.deepToString(network.getLatestAugmentingPath()) + "\n" +
                            "Graph: " + Arrays.deepToString(residualGraph));

            residualGraph = cloneGraph(network.getCurrentResidualGraph());
            pathFlow = network.step(source, sink);
        }
        assertEquals(23, flow, "max flow should be 23 : " + flow + " given \n\n\t");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkerson4() {
        network = new FlowNetwork(_graph4);
        int source = 0;
        int sink = 5;
        int flow = network.execute(source, sink);

        assertEquals(23, flow, "max flow should be 23 : " + flow + " given \n\n\t");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFordFulkersonStep4() {

        network = new FlowNetwork(_graph4);
        int source = 0;
        int sink = 5;
        int flow = 0;
        int[][] residualGraph = cloneGraph(_graph4);

        int pathFlow = network.step(source, sink);
        while (pathFlow > 0) {
            flow += pathFlow;

            // retrieve unique content
            HashSet<Integer> uniques = getUniques(network.getLatestAugmentingPath());
            assertEquals(2, uniques.size(),
                    "Latest augmenting path should have 2 values \n\n\t");

            assertTrue(networkIsSmallerThan(network.getCurrentFlow(), network.getGraph()),
                    "Current flow must be smaller than capacities.\n" +
                            "Flow:  " + Arrays.deepToString(network.getCurrentFlow()) + "\n" +
                            "Graph: " + Arrays.deepToString(network.getGraph()));

            assertTrue(networkIsSmallerThan(network.getLatestAugmentingPath(), residualGraph),
                    "Latest path must be smaller than residual graph.\n" +
                            "Path:  " + Arrays.deepToString(network.getLatestAugmentingPath()) + "\n" +
                            "Graph: " + Arrays.deepToString(residualGraph));

            residualGraph = cloneGraph(network.getCurrentResidualGraph());
            pathFlow = network.step(source, sink);
        }
        assertEquals(23, flow, "max flow should be 23 : " + flow + " given \n\n\t");
    }


    /**************************************
     * private auxiliary methods *
     *************************************/

    private int[][] cloneGraph(int[][] graph) {
        int[][] newGraph = null;
        if (graph.length > 0 && graph[0].length > 0) {
            newGraph = new int[graph.length][graph[0].length];

            for (int i = 0; i < graph.length; i++) {
                newGraph[i] = graph[i].clone();
            }
        }
        return newGraph;
    }

    /**
     * Analyzes a matrix and returns its unique elements as HashSet.
     *
     * @param arr matrix to be analyzed
     * @return unique elements of the matrix as HashSet
     */
    private HashSet<Integer> getUniques(int[][] arr) {
        HashSet<Integer> uniques = new HashSet<>();

        for (int[] line : arr) {
            for (int elem : line) {
                uniques.add(elem);
            }
        }

        return uniques;
    }

    /**
     * Compares two networks if a <= b.
     *
     * @param a network a
     * @param b network b
     * @return true if network a <= b, false otherwise.
     */
    private boolean networkIsSmallerThan(int[][] a, int[][] b) {
        // compare matrix size
        if (a.length > 0 && a.length == b.length) {
            if (a[0].length == b[0].length) {
                // check content
                for (int i = 0; i < a.length; i++) {
                    for (int j = 0; j < a[i].length; j++) {
                        if (a[i][j] > b[i][j]) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }
}
