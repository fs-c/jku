package expr;

public class Mul extends VariadicExpr {
    protected Mul(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        double value = 0;

        for (Expr operand : operands) {
            value *= operand.evaluate();
        }

        return value;
    }
}
