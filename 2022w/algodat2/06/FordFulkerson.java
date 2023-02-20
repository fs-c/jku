public interface FordFulkerson {
    int[][] getGraph();
    int[][] getCurrentResidualGraph();
    int[][] getLatestAugmentingPath();
    int[][] getCurrentFlow();

    /**
     * Perform a single flow augmenting iteration from source to sink
     * Update the latest augmenting path, the residual graph and the current flow by the maximum possible amount according to your chosen path.
     * The path must be chosen based on BFS.
     * @param source the source's vertex id
     * @param sink the sink's vertex id
     * @return the amount by which the flow has increased.
     */
    int step(int source, int sink);

    /**
     * Execute the ford-fulkerson algorithm (i.e., repeated calls of step())
     * @param source the source's vertex id
     * @param sink the sink's vertex id
     * @return the max flow from source to sink
     */
    int execute(int source, int sink);
}
