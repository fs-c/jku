package expr;

public abstract class Expr implements DotExportable {
  private static int lastId = -1;

  private int id;

  /**
   * Non-thread-safe constructor
   */
  Expr() {
    id = ++lastId;
  }

  /**
   * On creation every expression is assigned a unique ID.
   * @return The id.
   */
  int getId() {
    return id;
  }

  /**
   * A unique name based on the expression ID.
   * @return The unique expression ID.
   */
  String getNodeName() {
    return "expr_" + id;
  }

  /**
   * Evaluates the current expression and returns the result.
   * If this Expr contains child expressions, these are also evaluated and their results are combined (e.g., summed in case of Add).
   *
   * @return The evaluation result of this Expr.
   */
  public abstract double evaluate();
}
