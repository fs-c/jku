package ssw.mj.impl;

import ssw.mj.Errors.Message;
import ssw.mj.scanner.Token;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.Map;
import java.util.function.Supplier;

import static ssw.mj.Errors.Message.*;
import static ssw.mj.scanner.Token.Kind.*;

public final class Parser {

    /**
     * Maximum number of global variables per program
     */
    private static final int MAX_GLOBALS = 32767;

    /**
     * Maximum number of fields per class
     */
    private static final int MAX_FIELDS = 32767;

    /**
     * Maximum number of local variables per method
     */
    private static final int MAX_LOCALS = 127;

    private static final int ERROR_DISTANCE_HEURISTIC = 3;

    /**
     * Last recognized token;
     */
    private Token t;

    /**
     * Lookahead token (not recognized).)
     */
    private Token la;

    /**
     * Shortcut to kind attribute of lookahead token (la).
     */
    private Token.Kind sym;

    /**
     * Number of error-free scans, starts out at just above the minimum threshold for outputting errors.
     * (Can't set to 0 because we might lose initial errors, can't set to MAX_VALUE because we might overflow.)
     */
    private int errorDistance = ERROR_DISTANCE_HEURISTIC + 1;

    /**
     * According scanner
     */
    public final Scanner scanner;

    /**
     * According code buffer
     */
    public final Code code;

    /**
     * According symbol table
     */
    public final Tab tab;

    private static final Token.Kind[] firstConstDecl = { final_ };
    private static final Token.Kind[] firstVarDecl = { ident }; // Type
    private static final Token.Kind[] firstClassDecl = { class_ };
    private static final Token.Kind[] firstMethodDecl = { void_, ident }; // Type
    private static final Token.Kind[] firstFormPars = { ident }; // Type
    private static final Token.Kind[] firstType = { ident };
    private static final Token.Kind[] firstBlock = { lbrace };
    private static final Token.Kind[] firstStatement = { ident, if_, while_, break_, return_, read, print, lbrace, semicolon }; // Designator, Block
    private static final Token.Kind[] firstAssignop = { assign, plusas, minusas, timesas, slashas, remas };
    private static final Token.Kind[] firstActPars = { lpar };
    private static final Token.Kind[] firstExpr = { minus, ident, number, charConst, new_, lpar }; // Term
    private static final Token.Kind[] firstDesignator = { ident };
    private static final Token.Kind[] firstAddop = { plus, minus };
    private static final Token.Kind[] firstMulop = { times, slash, rem };

    private static final EnumSet<Token.Kind> recoverDeclSet = EnumSet.of(eof, lbrace, final_, ident, class_);
    private static final EnumSet<Token.Kind> recoverMethodDeclSet = EnumSet.of(eof, void_, ident);
    private static final EnumSet<Token.Kind> recoverStatementSet = EnumSet.of(eof, ident, if_, while_, break_, return_, read, print, lbrace, semicolon);

    public Parser(Scanner scanner) {
        this.scanner = scanner;
        tab = new Tab(this);
        code = new Code(this);
        // Pseudo token to avoid crash when 1st symbol has scanner error.
        la = new Token(none, 1, 1);
    }

    /**
     * Reads ahead one symbol.
     */
    private void scan() {
        t = la;
        la = scanner.next();
        sym = la.kind;
        errorDistance++;
    }

    /**
     * Verifies symbol and reads ahead.
     */
    private boolean check(Token.Kind expected) {
        if (sym == expected) {
            scan();
        } else {
            error(TOKEN_EXPECTED, expected);
        }

        return true;
    }

    /**
     * Adds error message to the list of errors.
     */
    public void error(Message msg, Object... msgParams) {
        if (errorDistance >= ERROR_DISTANCE_HEURISTIC) {
            scanner.errors.error(la.line, la.col, msg, msgParams);
            System.out.format("%s (%d:%d)\n", msg, la.line, la.col);
        }

        errorDistance = 0;
    }

    private void error(Message msg, Token.Kind[] expected) {
        error(msg, expected[0]);
    }

    /**
     * Starts the analysis.
     */
    public void parse() {
        scan();
        program();
        check(Token.Kind.eof);
    }

    private <T> boolean includes(T[] array, T key) {
        return Arrays.stream(array).anyMatch(sym -> sym == key);
    }

    // "program" ident { ConstDecl | VarDecl | ClassDecl } "{" { MethodDecl } "}".
    private void program() {
        // "program" ident
        check(Token.Kind.program);
        check(Token.Kind.ident);

        while (true) {
            // { ConstDecl | VarDecl | ClassDecl }
            runUntilFalse(() -> requireNone(Map.of(
                () -> includes(firstConstDecl, sym), this::constDecl,
                () -> includes(firstVarDecl, sym), this::varDecl,
                () -> includes(firstClassDecl, sym), this::classDecl
            )));

            if (sym == lbrace || sym == eof) {
                break;
            }

            recoverDecl();
        }

        // "{" { MethodDecl } "}"
        check(lbrace);
        while (true) {
            runUntilFalse(() -> requireNone(Map.of(
                    () -> includes(firstMethodDecl, sym), this::methodDecl
            )));

            if (sym == rbrace || sym == eof) {
                break;
            }

            recoverMethodDecl();
        }
        check(rbrace);
    }

    private void recoverDecl() {
        error(INVALID_DECL);

        do {
            scan();
        } while (!recoverDeclSet.contains(sym));

        errorDistance = 0;
    }

    private void recoverMethodDecl() {
        error(INVALID_METH_DECL);

        do {
            scan();
        } while (!recoverMethodDeclSet.contains(sym));

        errorDistance = 0;
    }

    // "final" Type ident "=" ( number | charConst ) ";".
    private void constDecl() {
        // "final" Type
        check(final_);
        requireOne(Map.of(() -> includes(firstType, sym), this::type), () -> error(TOKEN_EXPECTED, firstType));

        // ident "="
        check(ident);
        check(assign);

        // ( number | charConst ) ";"
        requireOne(Map.of(
            () -> sym == number, () -> check(number),
            () -> sym == charConst, () -> check(charConst)
        ), () -> error(CONST_DECL));
        check(semicolon);
    }

    // Type ident { "," ident } ";".
    private void varDecl() {
        // Type
        requireOne(Map.of(() -> includes(firstType, sym), this::type), () -> error(TOKEN_EXPECTED, firstType));

        // ident { "," ident } ";"
        check(ident);
        runUntilFalse(() -> optionalCombination(comma, ident));
        check(semicolon);
    }

    // "class" ident "{" { VarDecl } "}".
    private void classDecl() {
        // "class" ident
        check(class_);
        check(ident);

        // "{" { VarDecl } "}"
        check(lbrace);
        runUntilFalse(() -> requireNone(Map.of(
            () -> includes(firstVarDecl, sym), this::varDecl
        )));
        check(rbrace);
    }

    // ( Type | "void" ) ident "(" [ FormPars ] ")" { VarDecl } Block.
    private void methodDecl() {
        // ( Type | "void" )
        requireOne(Map.of(
            () -> includes(firstType, sym), this::type,
            () -> sym == void_, () -> check(void_)
        ), () -> error(INVALID_METH_DECL, sym));

        // ident "(" [ FormPars ] ")"
        check(ident);
        check(lpar);
        requireNone(Map.of(() -> includes(firstFormPars, sym), this::formPars));
        check(rpar);

        // { VarDecl }
        runUntilFalse(() -> requireNone(Map.of(() -> includes(firstVarDecl, sym), this::varDecl)));

        // Block
        requireOne(Map.of(() -> includes(firstBlock, sym), this::block), () -> error(TOKEN_EXPECTED, firstBlock));
    }

    private void type() {
        check(ident);

        if (sym == lbrack) {
            check(lbrack);
            check(rbrack);
        }
    }

    // Type ident { "," Type ident }.
    private void formPars() {
        // Type ident
        requireOne(Map.of(() -> includes(firstType, sym), this::type), () -> error(TOKEN_EXPECTED, firstType));
        check(ident);

        // { "," Type ident }
        runUntilFalse(() -> optionalCombination(() -> sym == comma, () -> check(comma), this::type, () -> check(ident)));
    }

    // "{" { Statement } "}".
    private void block() {
        // "{" { Statement } "}"
        check(lbrace);
        while (true) {
            runUntilFalse(() -> requireNone(Map.of(() -> includes(firstStatement, sym), this::statement)));

            if (sym == rbrace || sym == eof) {
                break;
            }

            recoverStatement();
        }
        check(rbrace);
    }

    private void recoverStatement() {
        error(INVALID_STAT);

        do {
            scan();
        } while (!recoverStatementSet.contains(sym));

        errorDistance = 0;
    }

    // Designator ( Assignop Expr | ActPars | "++" | "--" ) ";"
    //  | "if" "(" Condition ")" Statement [ "else" Statement ]
    //  | "while" "(" Condition ")" Statement
    //  | "break" ";"
    //  | "return" [ Expr ] ";"
    //  | "read" "(" Designator ")" ";"
    //  | "print" "(" Expr [ "," number ] ")" ";"
    //  | Block
    //  | ";".
    private void statement() {
        // Designator ( Assignop Expr | ActPars | "++" | "--" ) ";"
        final Runnable assignStatement = () -> combination(
            this::designator,
            () -> requireOne(Map.of(
                () -> includes(firstAssignop, sym), () -> combination(this::assignop, this::expr),
                () -> includes(firstActPars, sym), this::actPars,
                () -> sym == pplus, () -> check(pplus),
                () -> sym == mminus, () -> check(mminus)
            ), () -> error(DESIGN_FOLLOW)),
            () -> check(semicolon)
        );

        // "if" "(" Condition ")" Statement [ "else" Statement ]
        final Runnable ifStatement = () -> optionalCombination(
            // "if" "(" Condition ")" Statement
            () -> check(if_), () -> check(lpar), this::condition, () -> check(rpar), this::statement,
            // [ "else" Statement ]
            () -> requireNone(Map.of(() -> sym == else_, () -> optionalCombination(() -> check(else_), this::statement)))
        );

        // "while" "(" Condition ")" Statement
        final Runnable whileStatement = () -> optionalCombination(
            () -> check(while_), () -> check(lpar), this::condition, () -> check(rpar), this::statement
        );

        // "break" ";"
        final Runnable breakStatement = () -> optionalCombination(() -> check(break_), () -> check(semicolon));

        // "return" [ Expr ] ";"
        final Runnable returnStatement = () -> optionalCombination(
            () -> check(return_),
            () -> requireNone(Map.of(() -> includes(firstExpr, sym), this::expr)),
            () -> check(semicolon)
        );

        // "read" "(" Designator ")" ";"
        final Runnable readStatement = () -> optionalCombination(
            () -> check(read), () -> check(lpar), this::designator, () -> check(rpar), () -> check(semicolon)
        );

        // "print" "(" Expr [ "," number ] ")" ";"
        final Runnable printStatement = () -> optionalCombination(
            () -> check(print), () -> check(lpar), this::expr,
            () -> requireNone(Map.of(() -> sym == comma, () -> optionalCombination(() -> check(comma), () -> check(number)))),
            () -> check(rpar), () -> check(semicolon)
        );

        requireOne(Map.of(
            () -> includes(firstDesignator, sym), assignStatement,
            () -> sym == if_, ifStatement,
            () -> sym == while_, whileStatement,
            () -> sym == break_, breakStatement,
            () -> sym == return_, returnStatement,
            () -> sym == read, readStatement,
            () -> sym == print, printStatement,
            () -> sym == lbrace, this::block,
            () -> sym == semicolon, () -> check(semicolon)
        ), () -> error(INVALID_STAT));
    }

    // "=" | "+=" | "-=" | "*=" | "/=" | "%=".
    private void assignop() {
        requireOne(Map.of(
            () -> sym == assign, () -> check(assign),
            () -> sym == plusas, () -> check(plusas),
            () -> sym == minusas, () -> check(minusas),
            () -> sym == timesas, () -> check(timesas),
            () -> sym == slashas, () -> check(slashas),
            () -> sym == remas, () -> check(remas)
        ), () -> error(ASSIGN_OP));
    }

    // CondTerm { "||" CondTerm }.
    private void condition() {
        // CondTerm
        condTerm();

        // { "||" CondTerm }
        runUntilFalse(() -> optionalCombination(() -> sym == or, () -> check(or), this::condTerm));
    }

    // CondFact { "&&" CondFact }.
    private void condTerm() {
        // CondFact
        condFact();

        // { "&&" CondFact }
        runUntilFalse(() -> optionalCombination(() -> sym == and, () -> check(and), this::condFact));
    }

    // Expr Relop Expr.
    private void condFact() {
        combination(this::expr, this::relop, this::expr);
    }

    // "==" | "!=" | ">" | ">=" | "<" | "<=".
    private void relop() {
        requireOne(Map.of(
            () -> sym == eql, () -> check(eql),
            () -> sym == neq, () -> check(neq),
            () -> sym == gtr, () -> check(gtr),
            () -> sym == geq, () -> check(geq),
            () -> sym == lss, () -> check(lss),
            () -> sym == leq, () -> check(leq)
        ), () -> error(REL_OP));
    }

    // ident { "." ident | "[" Expr "]" }.
    private void designator() {
        check(ident);
        runUntilFalse(() ->
            optionalCombination(() -> sym == period, () -> check(period), () -> check(ident)) ||
            optionalCombination(() -> sym == lbrack, () -> check(lbrack), this::expr, () -> check(rbrack))
        );
    }

    // [ "–" ] Term { Addop Term }.
    private void expr() {
        // [ "–" ]
        requireNone(Map.of(() -> sym == minus, () -> check(minus)));

        // Term { Addop Term }
        term();
        runUntilFalse(() -> optionalCombination(() -> includes(firstAddop, sym), this::addop, this::term));
    }

    // "+" | "–".
    private void addop() {
        requireOne(Map.of(
            () -> sym == plus, () -> check(plus),
            () -> sym == minus, () -> check(minus)
        ), () -> error(ADD_OP, sym));
    }

    // Factor { Mulop Factor | "**" number }.
    private void term() {
        factor();
        runUntilFalse(() ->
            optionalCombination(() -> includes(firstMulop, sym), this::mulop, this::factor) ||
            optionalCombination(() -> sym == exp, () -> check(exp), () -> check(number))
        );
    }

    // "*" | "/" | "%".
    private void mulop() {
        requireOne(Map.of(
            () -> sym == times, () -> check(times),
            () -> sym == slash, () -> check(slash),
            () -> sym == rem, () -> check(rem)
        ), () -> error(MUL_OP, sym));
    }

    // Designator [ ActPars ] | number | charConst | "new" ident [ "[" Expr "]" ] | "(" Expr ")".
    private void factor() {
        requireOne(Map.of(
            // Designator [ ActPars ]
            () -> includes(firstDesignator, sym), () -> combination(
                this::designator, () -> requireNone(Map.of(() -> includes(firstActPars, sym), this::actPars))
            ),
            // number
            () -> sym == number, () -> check(number),
            // charConst
            () -> sym == charConst, () -> check(charConst),
            // "new" ident [ "[" Expr "]" ]
            () -> sym == new_, () -> optionalCombination(
                () -> check(new_), () -> check(ident), () -> requireNone(Map.of(
                    () -> sym == lbrack, () -> optionalCombination(() -> check(lbrack), this::expr, () -> check(rbrack))
                ))
            ),
            // "(" Expr ")"
            () -> sym == lpar, () -> optionalCombination(() -> check(lpar), this::expr, () -> check(rpar))
        ), () -> error(INVALID_FACT));
    }

    // "(" [ Expr { "," Expr } ] ")".
    private void actPars() {
        check(lpar);
        requireNone(Map.of(() -> includes(firstExpr, sym), this::expr));
        runUntilFalse(() -> optionalCombination(() -> sym == comma, () -> check(comma), this::expr));
        check(rpar);
    }

    /**
     * when wrapping one of the helpers, effectively turns it into { ... }
     */
    private void runUntilFalse(Supplier<Boolean> fn) {
        while (fn.get()) {}
    }

    /**
     * equivalent to [ A B ... ]
     */
    private boolean optionalCombination(Token.Kind... tokens) {
        final var match = sym == tokens[0];
        if (match) {
            Arrays.stream(tokens).forEach(this::check);
        }

        return match;
    }

    /**
     * equivalent to [ A B ... ]
     */
    private boolean optionalCombination(Supplier<Boolean> initial, Runnable... actions) {
        final var match = initial.get();
        if (match) {
            combination(actions);
        }

        return match;
    }

    /**
     * equivalent to A B ...
     */
    private void combination(Runnable... actions) {
        Arrays.stream(actions).forEach(Runnable::run);
    }

    /**
     * see requireOne, but equivalent to [ A | B | ... ]
     */
    private boolean requireNone(Map<Supplier<Boolean>, Runnable> cases) {
        return requireOne(cases, () -> {});
    }

    /**
     * accepts a map of predicates -> actions, runs any action whose predicate returns true. if no action is run, runs
     * the error predicate and returns false. otherwise returns true.
     * used to describe 'A | B | ...', where the predicate checks first(X) and the action is X.
     */
    private boolean requireOne(Map<Supplier<Boolean>, Runnable> cases, Runnable error) {
        // this pattern is probably stupidly inefficient but let's not pretend this is a real compiler

        for (final var entry : cases.entrySet()) {
            final var predicate = entry.getKey();
            final var action = entry.getValue();

            if (predicate.get()) {
                action.run();
                return true;
            }
        }


        error.run();
        return false;
    }

    // ===============================================
    // TODO Exercise 3: Error recovery methods
    // TODO Exercise 4: Symbol table handling
    // TODO Exercise 5-6: Code generation
    // ===============================================

    // TODO Exercise 3: Error distance

    // TODO Exercise 2 + Exercise 3: Sets to handle certain first, follow, and recover sets

    // ---------------------------------
    // ------------------------------------

    // TODO Exercise 3: Error recovery methods: recoverDecl, recoverMethodDecl and recoverStat

    // ====================================
    // ====================================
}
