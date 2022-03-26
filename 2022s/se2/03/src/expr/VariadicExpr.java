package expr;

import java.util.function.BiFunction;

public abstract class VariadicExpr extends Expr {
    final Expr[] expressions;

    VariadicExpr(Expr[] expressions) {
        this.expressions = expressions;
    }

    double evaluate(double startingPoint, BiFunction<Double, Double, Double> operation) {
        double value = startingPoint;

        for (Expr e : expressions) {
            value = operation.apply(value, e.evaluate());
        }

        return value;
    }

    @Override
    public String asDotString(boolean useDashedEdges) {
        StringBuilder joined = new StringBuilder();

        for (Expr e : expressions) {
            joined.append(e.asDotString())
                    .append(DotExportable.formatEdge(getId(), e.getId(), useDashedEdges));
        }

        return joined.toString();
    }
}
