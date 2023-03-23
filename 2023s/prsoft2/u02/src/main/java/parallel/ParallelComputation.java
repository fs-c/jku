package parallel;

import textanalysis.Settings;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;

public class ParallelComputation<R, P extends Problem<R, P>> {
    public R compute(P problem) {
        var initialTask = new ProblemRecursiveTask<R, P>(problem);

        return new ForkJoinPool(Settings.parallelism).invoke(initialTask);
    }
}
