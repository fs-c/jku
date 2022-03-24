package expr;

public class Div extends BinaryExpr {
    public Div(Expr left, Expr right) {
        super(left, right);
    }

    @Override
    public double evaluate() {
        return left.evaluate() / right.evaluate();
    }
}
