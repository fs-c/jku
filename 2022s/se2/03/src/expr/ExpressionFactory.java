package expr;

public class ExpressionFactory {
  /* TODO public factory methods */

    public static Add add(Expr ...e) {
        return new Add(e);
    }

    public static Sub sub(Expr left, Expr right) {
        return new Sub(left, right);
    }

    public static Const con(double v) {
        return new Const(v);
    }
}
