package expr;

public class ExpressionFactory {
    public static Add add(Expr ...e) {
        return new Add(e);
    }

    public static Sub sub(Expr left, Expr right) {
        return new Sub(left, right);
    }

    public static Mul mul(Expr ...e) {
        return new Mul(e);
    }

    public static Div div(Expr left, Expr right) {
        return new Div(left, right);
    }

    public static Const con(double v) {
        return new Const(v);
    }
}
