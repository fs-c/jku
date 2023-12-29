package ssw.mj.impl;

import ssw.mj.Errors.Message;
import ssw.mj.codegen.Operand;
import ssw.mj.scanner.Token;
import ssw.mj.symtab.Obj;
import ssw.mj.symtab.Struct;

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

    private static final String MAIN_METHOD_NAME = "main";

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
        final var programObject = tab.insert(Obj.Kind.Prog, t.val, Tab.noType);

        tab.openScope();

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

        code.dataSize = tab.curScope.nVars();

        if (tab.curScope.nVars() > MAX_GLOBALS) {
            error(TOO_MANY_GLOBALS);
        }

        var mainMethodAdded = false;

        // "{" { MethodDecl } "}"
        check(lbrace);
        while (true) {
            if (includes(firstMethodDecl, sym)) {
                final var method = methodDecl();
                if (method.name.equals(MAIN_METHOD_NAME)) {
                    mainMethodAdded = true;
                }
            } else if (sym == rbrace || sym == eof) {
                break;
            } else {
                recoverMethodDecl();
            }
        }
        check(rbrace);

        if (!mainMethodAdded) {
            error(METH_NOT_FOUND, MAIN_METHOD_NAME);
        }

        programObject.locals = tab.curScope.locals();
        tab.closeScope();
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
        var type = Tab.noType;

        // "final" Type
        check(final_);
        if (includes(firstType, sym)) {
            type = type();
        } else {
            error(TOKEN_EXPECTED, firstType);
        }

        // ident "="
        check(ident);
        final var typeObject = tab.insert(Obj.Kind.Con, t.val, type);
        check(assign);

        final var typeKind = type.kind;

        // ( number | charConst ) ";"
        requireOne(Map.of(
            () -> sym == number, () -> {
                    if (typeKind == Struct.Kind.Int) {
                        check(number);
                        typeObject.val = Integer.parseInt(t.val);
                    } else {
                        error(CONST_TYPE);
                    }
                },
            () -> sym == charConst, () -> {
                    if (typeKind == Struct.Kind.Char) {
                        check(charConst);
                        typeObject.val = t.numVal;
                    } else {
                        error(CONST_TYPE);
                    }
                }
        ), () -> error(CONST_DECL));
        check(semicolon);
    }

    // Type ident { "," ident } ";".
    private void varDecl() {
        // Type
        final var type = type();

        // ident
        check(ident);
        tab.insert(Obj.Kind.Var, t.val, type);

        // { "," ident }
        while (sym == comma) {
            check(comma);
            check(ident);
            tab.insert(Obj.Kind.Var, t.val, type);
        }

        // ";"
        check(semicolon);
    }

    // "class" ident "{" { VarDecl } "}".
    private void classDecl() {
        // "class" ident
        check(class_);
        check(ident);

        final var classObject = tab.insert(Obj.Kind.Type, t.val, new Struct(Struct.Kind.Class));

        // "{"
        check(lbrace);
        tab.openScope();

        // { VarDecl }
        runUntilFalse(() -> requireNone(Map.of(
            () -> includes(firstVarDecl, sym), this::varDecl
        )));

        if (tab.curScope.nVars() > MAX_FIELDS) {
            error(TOO_MANY_FIELDS);
        }

        classObject.type.fields = tab.curScope.locals();

        // "}"
        check(rbrace);
        tab.closeScope();
    }

    // ( Type | "void" ) ident "(" [ FormPars ] ")" { VarDecl } Block.
    private Obj methodDecl() {
        var type = Tab.noType;

        // ( Type | "void" )
        if (sym == ident) {
            type = type();

            if (type.isRefType()) {
                error(INVALID_METH_RETURN_TYPE);
            }
        } else if (sym == void_) {
            check(void_);
        } else {
            error(INVALID_METH_DECL, sym);
        }

        // ident
        check(ident);
        final var methodObject = tab.insert(Obj.Kind.Meth, t.val, type);
        methodObject.adr = code.pc;

        // "(" [ FormPars ] ")"
        check(lpar);
        tab.openScope();
        if (includes(firstFormPars, sym)) {
            methodObject.nPars = formPars();
        }
        check(rpar);

        if (methodObject.name.equals(MAIN_METHOD_NAME)) {
            // why is this not mainPc :(
            code.mainpc = code.pc;

            if (type != Tab.noType) {
                error(MAIN_NOT_VOID);
            }

            if (methodObject.nPars != 0) {
                error(MAIN_WITH_PARAMS);
            }

            if (tab.curScope.nVars() > 0) {
                error(MAIN_WITH_PARAMS);
            }

            if (type != Tab.noType) {
                error(MAIN_NOT_VOID);
            }
        }

        methodObject.nPars = tab.curScope.nVars();

        // { VarDecl }
        runUntilFalse(() -> requireNone(Map.of(() -> includes(firstVarDecl, sym), this::varDecl)));

        methodObject.locals = tab.curScope.locals();
        methodObject.adr = code.pc;

        if (tab.curScope.nVars() > MAX_LOCALS) {
            error(TOO_MANY_LOCALS);
        }

        code.methodEnter(methodObject.nPars, tab.curScope.nVars());

        // Block
        requireOne(Map.of(() -> includes(firstBlock, sym), this::block), () -> error(TOKEN_EXPECTED, firstBlock));

        code.methodExit();

        if (methodObject.type != Tab.noType) {
            code.put(Code.OpCode.trap);
            code.put(1);
        }

        tab.closeScope();

        return methodObject;
    }

    private Struct type() {
        check(ident);

        Obj typeObject = tab.find(t.val);
        if (typeObject.kind != Obj.Kind.Type) {
            error(NO_TYPE);
        }

        final var type = typeObject.type;

        if (sym == lbrack) {
            check(lbrack);
            check(rbrack);

            // this is terrible, should be Struct.createArrayOf(type) or something
            return new Struct(type);
        }

        return type;
    }

    // Type ident { "," Type ident }.
    private int formPars() {
        int numPars = 1;

        // Type ident
        if (includes(firstType, sym)) {
            final var type = type();
            check(ident);
            tab.insert(Obj.Kind.Var, t.val, type);
        } else {
            error(TOKEN_EXPECTED, firstType);
        }

        // { "," Type ident }
        while (sym == comma) {
            check(comma);

            // Type ident
            if (includes(firstType, sym)) {
                final var type = type();
                check(ident);
                tab.insert(Obj.Kind.Var, t.val, type);
            } else {
                error(TOKEN_EXPECTED, firstType);
            }

            numPars++;
        }

        return numPars;
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
        final Runnable assignStatement = () -> {
            final var x = designator();

            switch (sym) {
                case assign, plusas, minusas, timesas, slashas, remas -> {
                    if (x.obj != null && x.obj.kind != Obj.Kind.Var) {
                        error(CANNOT_ASSIGN_TO, x.obj.kind);
                    }

                    if (x.kind == Operand.Kind.Con) {
                        error(CANNOT_ASSIGN_TO, x.kind);
                    }

                    final var compoundOperation = assignop();
                    if (compoundOperation != Code.OpCode.nop) {
                        code.compoundAssignmentPrepare(x);
                    }

                    final var y = expr();

                    if (compoundOperation != Code.OpCode.nop && (x.type != Tab.intType || y.type != Tab.intType)) {
                        error(NO_INT_OPERAND);
                    }

                    if (y == null || !y.type.assignableTo(x.type)) {
                        error(INCOMP_TYPES);
                    }

                    if (compoundOperation == Code.OpCode.nop) {
                        code.assign(x, y);
                    } else {
                        code.load(y);
                        code.put(compoundOperation);
                        code.assign(x, null);
                    }

                }
                case lpar -> actPars();
                case pplus, mminus -> {
                    if (x.type != Tab.intType) {
                        error(NO_INT_OPERAND);
                    }

                    code.compoundAssignmentPrepare(x);
                    code.inc(x, sym == pplus ? 1 : -1);

                    scan();
                }
                default -> error(DESIGN_FOLLOW);
            }

            check(semicolon);
        };

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
        final Runnable returnStatement = () -> {
            check(return_);

            if (sym != semicolon) {
                final var x = expr();

                code.load(x);
            }

            check(semicolon);
        };

        // "read" "(" Designator ")" ";"
        final Runnable readStatement = () -> {
            check(read);
            check(lpar);

            final var x = designator();
            if (x.type != Tab.intType && x.type != Tab.charType) {
                error(READ_VALUE);
            }

            code.put(x.type == Tab.intType ? Code.OpCode.read : Code.OpCode.bread);
            code.assign(x, null);

            check(rpar);
            check(semicolon);
        };

        // "print" "(" Expr [ "," number ] ")" ";"
        final Runnable printStatement = () -> {
            check(print);
            check(lpar);

            final var x = expr();
            if (x.type != Tab.intType && x.type != Tab.charType) {
                error(PRINT_VALUE);
            }

            code.load(x);

            if (sym == comma) {
                check(comma);
                check(number);
                code.load(new Operand(t.numVal));
            } else {
                code.loadConst(0);
            }

            code.put(x.type == Tab.intType ? Code.OpCode.print : Code.OpCode.bprint);

            check(rpar);
            check(semicolon);
        };

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
    private Code.OpCode assignop() {
        switch (sym) {
            case assign -> {
                check(assign);
                return Code.OpCode.nop;
            }
            case plusas -> {
                check(plusas);
                return Code.OpCode.add;
            }
            case minusas -> {
                check(minusas);
                return Code.OpCode.sub;
            }
            case timesas -> {
                check(timesas);
                return Code.OpCode.mul;
            }
            case slashas -> {
                check(slashas);
                return Code.OpCode.div;
            }
            case remas -> {
                check(remas);
                return Code.OpCode.rem;
            }
            default -> {
                error(ASSIGN_OP);
                return Code.OpCode.nop;
            }
        }
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
    private Operand designator() {
        check(ident);

        final var object = tab.find(t.val);
        var x = new Operand(object, this);

        while (sym == period || sym == lbrack) {
            if (sym == period) {
                if (x.type.kind != Struct.Kind.Class) {
                    error(NO_CLASS);
                }

                check(period);
                check(ident);

                code.load(x);

                final var field = tab.findField(t.val, x.type);
                if (field == null) {
                    break;
                }

                x.kind = Operand.Kind.Fld;
                x.type = field.type;
                x.adr = field.adr;
            } else {
                check(lbrack);

                code.load(x);

                Operand y = expr();
                if (y.type.kind != Struct.Kind.Int) {
                    error(ARRAY_INDEX);
                }

                if (x.type.kind != Struct.Kind.Arr) {
                    error(NO_ARRAY);
                }

                code.load(y);

                x.kind = Operand.Kind.Elem;
                x.type = x.type.elemType;

                check(rbrack);
            }
        }

        return x;
    }

    // [ "–" ] Term { Addop Term }.
    private Operand expr() {
        // [ "–" ]
        var shouldNegate = false;
        if (sym == minus) {
            check(minus);
            shouldNegate = true;
        }

        // Term
        final var x = term();

        if (shouldNegate) {
            if (x.type != Tab.intType) {
                error(NO_INT_OPERAND);
            }

            if (x.kind == Operand.Kind.Con) {
                x.val = -x.val;
            } else {
                code.load(x);
                code.put(Code.OpCode.neg);
            }
        }

        // { Addop Term }
        while (includes(firstAddop, sym)) {
            code.load(x);

            final var operation = addop();
            final var y = term();
            if (y == null) {
                // todo-null-checks
                break;
            }

            if (x.type != Tab.intType || y.type != Tab.intType) {
                error(NO_INT_OPERAND);
            }

            code.load(y);
            code.put(operation);
        }

        return x;
    }

    // "+" | "–".
    private Code.OpCode addop() {
        if (sym == plus) {
            check(plus);
            return Code.OpCode.add;
        } else if (sym == minus) {
            check(minus);
            return Code.OpCode.sub;
        } else {
            error(ADD_OP);
            return Code.OpCode.add;
        }
    }

    // Factor { Mulop Factor | "**" number }.
    private Operand term() {
        final var x = factor();

        while (includes(firstMulop, sym) || sym == exp) {
            code.load(x);

            if (sym == exp) {
                check(exp);
                check(number);

                for (var i = 0; i < t.numVal - 1; i++) {
                    code.put(Code.OpCode.dup);
                }

                for (var i = 0; i < t.numVal - 1; i++) {
                    code.put(Code.OpCode.mul);
                }

                if (t.numVal == 0) {
                    code.put(Code.OpCode.pop);
                    code.loadConst(1);
                }
            } else {
                final var operation = mulop();
                final var y = factor();

                if (y.type != Tab.intType) {
                    error(NO_INT_OPERAND);
                }

                code.load(y);
                code.put(operation);
            }

            if (x.type != Tab.intType) {
                error(NO_INT_OPERAND);
            }
        }

        return x;
    }

    // "*" | "/" | "%".
    private Code.OpCode mulop() {
        if (sym == times) {
            check(times);
            return Code.OpCode.mul;
        } else if (sym == slash) {
            check(slash);
            return Code.OpCode.div;
        } else if (sym == rem) {
            check(rem);
            return Code.OpCode.rem;
        } else {
            error(MUL_OP);
            return Code.OpCode.mul;
        }
    }

    // Designator [ ActPars ] | number | charConst | "new" ident [ "[" Expr "]" ] | "(" Expr ")".
    private Operand factor() {
        Operand x = null;

        switch (sym) {
            case ident -> {
                x = designator();

                if (sym == lpar) {
                    if (x.kind == Operand.Kind.Meth && x.type == Tab.noType) {
                        error(INVALID_CALL);
                    }

                    // todo: fix this once method calls are implemented, this makes symbol table tests happy for now
                    x.kind = Operand.Kind.Stack;

                    actPars();
                }
            }
            case number -> {
                check(number);

                x = new Operand(t.numVal);
            }
            case charConst -> {
                check(charConst);

                x = new Operand(t.numVal);
                x.type = Tab.charType;
            }
            case new_ -> {
                check(new_);
                check(ident);

                final var object = tab.find(t.val);
                if (object.kind != Obj.Kind.Type) {
                    error(NO_TYPE);
                    break;
                }

                var type = object.type;

                if (sym == lbrack) {
                    check(lbrack);

                    final var y = expr();
                    if (y.type.kind != Struct.Kind.Int) {
                        error(ARRAY_SIZE);
                    }

                    code.load(y);

                    code.put(Code.OpCode.newarray);
                    if (object.type.kind == Struct.Kind.Char) {
                        code.put(0);
                    } else {
                        code.put(1);
                    }

                    // this constructor signature is still absolutely moronic
                    type = new Struct(type);

                    check(rbrack);
                } else {
                    if (object.type.kind != Struct.Kind.Class) {
                        error(NO_CLASS_TYPE);
                    }

                    code.put(Code.OpCode.new_);
                    code.put2(object.type.nrFields());
                }

                x = new Operand(type);
            }
            case lpar -> {
                check(lpar);
                x = expr();
                check(rpar);
            }
            default -> error(INVALID_FACT);
        }

        return x;
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
