package expr;

public class Add extends VariadicExpr {
    protected Add(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        double value = 0;

        for (Expr operand : operands) {
            value += operand.evaluate();
        }

        return value;
    }
}
