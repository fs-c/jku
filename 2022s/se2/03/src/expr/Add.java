package expr;

public class Add extends VariadicExpr {
    Add(Expr[] operands) {
        super(operands);
    }

    @Override
    public double evaluate() {
        double value = 0;

        for (Expr e : expressions) {
            value += e.evaluate();
        }

        return value;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "+", evaluate(), "circle", "green")
                + super.asDotString(useDashedEdges);
    }
}
