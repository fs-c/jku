import java.util.*;

public class FlowNetwork implements FordFulkerson {
	// do not modify the next six lines
    private int[][] graph;
    private int[][] currentResidualGraph;
    private int[][] latestAugmentingPath;
    private int[][] currentFlow;
    private int nRows;
    private int nCols;

    FlowNetwork(int[][] graph) {
        nRows = graph.length;
        if (nRows > 0) {			
			this.graph = graph;
            nCols = graph[0].length;
            if (nCols > 0) {
                currentResidualGraph = new int[nRows][nCols];
                for (int row = 0; row < nRows; row++) {
                    currentResidualGraph[row] = graph[row].clone();
                }

                latestAugmentingPath = new int[nRows][nCols];
                currentFlow = new int[nRows][nCols];
            }
        }
    }

    @Override
    public int step(int source, int sink) {
        // using breadth first search, find a path from source to sink that has available capacity
        // if no path is found, return -1

        var path = new int[nRows];
        if (!bfs(path, source, sink)) {
            return -1;
        }

        // find the largest possible flow along this path

        int flow = Integer.MAX_VALUE;
        for (int v = sink; v != source; v = path[v]) {
            flow = Math.min(flow, currentResidualGraph[path[v]][v]);
        }

        // build the latest augmenting path and adjust the residual and current flow graphs
        // according to the path and flow obtained previously

        for (int[] row : latestAugmentingPath) {
            Arrays.fill(row, 0);
        }

        for (int v = sink; v != source; v = path[v]) {
            int u = path[v];

            latestAugmentingPath[u][v] = flow;

            currentFlow[u][v] += flow;

            currentResidualGraph[u][v] -= flow;
            currentResidualGraph[v][u] += flow;
        }

        // we're done, return flow

        return flow;
    }

    @Override
    public int execute(int source, int sink) {
        // execute step until it indicates that no further steps are possible
        // keep track of the maximum flow and return it

        int flow;
        int max_flow = 0;
        while ((flow = step(source, sink)) != -1) {
            max_flow += flow;
        }

        return max_flow;
    }

    @Override
    public int[][] getGraph() {
        return graph;
    }

    @Override
    public int[][] getCurrentResidualGraph() {
        return currentResidualGraph;
    }

    @Override
    public int[][] getLatestAugmentingPath() {
        return latestAugmentingPath;
    }

    @Override
    public int[][] getCurrentFlow() {
        return currentFlow;
    }

    /**************************************
     * private auxiliary methods *
     *************************************/
	 
	// TODO you may add further helper methods such as BFS search

    // finds a path with available capacity using breadth-first search of the current residual graph
    // returns true if a path was found, false otherwise
    boolean bfs(int[] path, int from, int to) {
        var queue = new ArrayDeque<Integer>(path.length);
        var visited = new boolean[path.length];

        queue.push(from);
        visited[from] = true;

        while (!queue.isEmpty() && !visited[to]) {
            // vertex we are currently looking at
            int v = queue.pop();

            // iterate vertices that might have an edge with the current vertex
            for (int i = 0; i < currentResidualGraph[v].length; i++) {
                // if there is an edge, and we haven't visited the other vertex yet, add it to the path and queue it up
                if (!visited[i] && currentResidualGraph[v][i] > 0) {
                    path[i] = v;
                    visited[i] = true;
                    queue.push(i);
                }
            }
        }

        return visited[to];
    }
}
