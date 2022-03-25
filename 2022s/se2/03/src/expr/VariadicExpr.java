package expr;

public abstract class VariadicExpr extends Expr {
    final Expr[] expressions;

    VariadicExpr(Expr[] expressions) {
        this.expressions = expressions;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        StringBuilder joined = new StringBuilder();

        for (Expr e : expressions) {
            joined.append(e.asDotString())
                    .append(DotExportable.formatLine(getId(), e.getId(), useDashedEdges));
        }

        return joined.toString();
    }
}
