package expr;

import java.util.function.BiFunction;

public abstract class BinaryExpr extends Expr {
    final Expr left;
    final Expr right;

    BinaryExpr(Expr left, Expr right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return left.asDotString(useDashedEdges) + DotExportable.formatEdge(getId(), left.getId(), useDashedEdges)
                + right.asDotString(useDashedEdges) + DotExportable.formatEdge(getId(), right.getId(), useDashedEdges);
    }
}
