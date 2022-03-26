package expr;

import java.util.Arrays;
import java.util.Objects;

public class ExpressionFactory {
    public static Add add(Expr ...e) {
        if (e == null || Arrays.stream(e).anyMatch(Objects::isNull) || e.length < 2) {
            throw new IllegalArgumentException();
        }

        return new Add(e);
    }

    public static Sub sub(Expr left, Expr right) {
        if (left == null || right == null) {
            throw new IllegalArgumentException();
        }

        return new Sub(left, right);
    }

    public static Mul mul(Expr ...e) {
        if (e == null || Arrays.stream(e).anyMatch(Objects::isNull) || e.length < 2) {
            throw new IllegalArgumentException();
        }

        return new Mul(e);
    }

    public static Div div(Expr left, Expr right) {
        if (left == null || right == null) {
            throw new IllegalArgumentException();
        }

        return new Div(left, right);
    }

    public static Const con(double v) {
        return new Const(v);
    }
}
