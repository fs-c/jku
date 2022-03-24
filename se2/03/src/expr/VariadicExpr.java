package expr;

public abstract class VariadicExpr extends Expr {
    final Expr[] operands;

    protected VariadicExpr(Expr[] operands) {
        this.operands = operands;
    }
}
