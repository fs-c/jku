package expr;

public abstract class BinaryExpr extends Expr {
    final Expr left;
    final Expr right;

    BinaryExpr(Expr left, Expr right) {
        this.left = left;
        this.right = right;
    }
}
