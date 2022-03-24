package expr.calc;

import expr.Expr;

import static expr.ExpressionFactory.*;

public class ExprCalculator {
    public static void main(String[] args) {
        Expr e = add(sub(add(con(10), con(10)), con(7)), con(5));

        System.out.print(e.evaluate());

        /* TODO make the following work using the ExpressionFactory */
        /*Expr e =
          add(
            con(5),
            add(
              sub(
                div(con(1234.56), con(78.9)
                ),
                con(17.17)
              ),
              mul(con(5), con(7), con(1.5)),
              con(1)
            ));

        System.out.println("Default:");
        System.out.println(e.asDotString());

        System.out.println("Explicit false:");
        System.out.println(e.asDotString(false));

        System.out.println("Explicit true:");
        System.out.println(e.asDotString(true));*/

        /* TODO make your own example that uses each expression type at least once.
        * Submit the visualization of this expression as part of your exercise submission.
        * You can enter your DOT description into the digraph
        * at https://dreampuf.github.io/GraphvizOnline/#digraph%20G%20%7B%0A%0A%7D */
    }
}
