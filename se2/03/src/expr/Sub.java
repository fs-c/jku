package expr;

public class Sub extends BinaryExpr {
    public Sub(Expr left, Expr right) {
        super(left, right);
    }

    @Override
    public double evaluate() {
        return left.evaluate() - right.evaluate();
    }
}
