package expr;

public class Sub extends BinaryExpr {
    Sub(Expr left, Expr right) {
        super(left, right);
    }

    @Override
    public double evaluate() {
        return left.evaluate() - right.evaluate();
    }

    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "-", evaluate(), "circle", "lightblue")
                + super.asDotString(useDashedEdges);
    }
}
