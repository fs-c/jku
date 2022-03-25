package expr;

public abstract class BinaryExpr extends Expr {
    final Expr left;
    final Expr right;

    BinaryExpr(Expr left, Expr right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        return left.asDotString(useDashedEdges) + DotExportable.formatLine(getId(), left.getId(), useDashedEdges)
                + right.asDotString(useDashedEdges) + DotExportable.formatLine(getId(), right.getId(), useDashedEdges);
    }
}
