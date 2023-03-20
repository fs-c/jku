package parallel;

import java.util.concurrent.RecursiveTask;

public class ProblemRecursiveTask<R, P extends Problem<R, P>> extends RecursiveTask<R> {
    private P problem;

    ProblemRecursiveTask(P problem) {
        this.problem = problem;
    }

    @Override
    protected R compute() {
        if (problem.isSmall()) {
            return problem.solveSequential();
        }

        var subProblems = problem.split();
        var firstTask = new ProblemRecursiveTask<R, P>(subProblems.fst()).fork();
        var secondTask = new ProblemRecursiveTask<R, P>(subProblems.snd()).fork();

        return problem.combine(firstTask.join(), secondTask.join());
    }
}
