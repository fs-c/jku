package expr.calc;

import expr.Expr;

import static expr.ExpressionFactory.*;

public class ExprCalculator {
    public static void main(String[] args) {
        Expr e = div(sub(add(con(100), con(40), con(15)), mul(con(4), con(12), add(con(4), con(12)))), con(3));

        System.out.println("Default:");
        System.out.println(e.asDotString());

        System.out.println("Explicit false:");
        System.out.println(e.asDotString(false));

        System.out.println("Explicit true:");
        System.out.println(e.asDotString(true));
    }
}
