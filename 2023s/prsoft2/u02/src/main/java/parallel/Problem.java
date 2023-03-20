package parallel;

public interface Problem<R, P extends Problem<R, P>> {
  boolean isSmall();
  Pair<P, P> split();
  R combine(R result1, R result2);
  R solveSequential();
}
