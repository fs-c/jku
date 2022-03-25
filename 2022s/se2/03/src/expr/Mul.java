package expr;

public class Mul extends VariadicExpr {
    Mul(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        double value = 1;

        for (Expr e : expressions) {
            value *= e.evaluate();
        }

        return value;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "*", evaluate(), "circle", "yellow")
                + super.asDotString(useDashedEdges);
    }
}
