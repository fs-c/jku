package expr;

public class Add extends VariadicExpr {
    Add(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        return super.evaluate(0, Double::sum);
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "+", evaluate(), "circle", "green")
                + super.asDotString(useDashedEdges);
    }
}
