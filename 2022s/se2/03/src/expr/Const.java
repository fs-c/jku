package expr;

public class Const extends Expr {
    private final double value;

    Const(double val) {
        value = val;
    }

    @Override
    public double evaluate() {
        return value;
    }
}
