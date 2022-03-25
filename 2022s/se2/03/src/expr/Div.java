package expr;

public class Div extends BinaryExpr {
    Div(Expr left, Expr right) {
        super(left, right);
    }

    @Override
    public double evaluate() {
        return left.evaluate() / right.evaluate();
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return DotExportable.formatNode(getId(), "/", evaluate(), "circle", "red")
                + super.asDotString(useDashedEdges);
    }
}
