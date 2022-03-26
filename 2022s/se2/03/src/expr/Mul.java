package expr;

public class Mul extends VariadicExpr {
    Mul(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        return super.evaluate(1, (x, y) -> x * y);
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "*", evaluate(), "circle", "yellow")
                + super.asDotString(useDashedEdges);
    }
}
