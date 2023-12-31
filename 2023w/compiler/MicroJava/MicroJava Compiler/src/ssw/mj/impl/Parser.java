package ssw.mj.impl;

import ssw.mj.Errors.Message;
import ssw.mj.codegen.Label;
import ssw.mj.codegen.Operand;
import ssw.mj.scanner.Token;
import ssw.mj.symtab.Obj;
import ssw.mj.symtab.Struct;

import java.util.*;
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

    private String currentMethodName = null;

    public Parser(Scanner scanner) {
        this.scanner = scanner;
        tab = new Tab(this);
        code = new Code(this, tab);
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

        currentMethodName = t.val;

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
        while (includes(firstVarDecl, sym)) {
            varDecl();
        }

        methodObject.locals = tab.curScope.locals();
        methodObject.adr = code.pc;

        if (tab.curScope.nVars() > MAX_LOCALS) {
            error(TOO_MANY_LOCALS);
        }

        code.put(Code.OpCode.enter);
        code.put(methodObject.nPars);
        code.put(tab.curScope.nVars());

        // Block
        requireOne(Map.of(() -> includes(firstBlock, sym), () -> block(null)), () -> error(TOKEN_EXPECTED, firstBlock));

        if (methodObject.type == Tab.noType) {
            // voids don't need to contain a return statement, fake one at the end
            code.put(Code.OpCode.exit);
            code.put(Code.OpCode.return_);
        } else {
            // non-voids need to return something, runtime error (trap) if they don't
            code.put(Code.OpCode.trap);
            code.put(1);
        }

        tab.closeScope();

        currentMethodName = null;

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
        // Type ident
        final Runnable parameter = () -> {
            if (includes(firstType, sym)) {
                final var type = type();

                check(ident);

                tab.insert(Obj.Kind.Var, t.val, type);
            } else {
                error(TOKEN_EXPECTED, firstType);
            }
        };

        int numPars = 1;

        parameter.run();

        // { "," Type ident }
        while (sym == comma) {
            check(comma);
            parameter.run();
            numPars++;
        }

        return numPars;
    }

    // "{" { Statement } "}".
    private void block(Label endOfBlock) {
        // "{" { Statement } "}"
        check(lbrace);
        while (true) {
            while (includes(firstStatement, sym)) {
                statement(endOfBlock);
            }

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
    private void statement(Label breakLabel) {
        // Designator ( Assignop Expr | ActPars | "++" | "--" ) ";"
        final Runnable designatorStatement = () -> {
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

                        if (x.kind != Operand.Kind.Fld && x.kind != Operand.Kind.Elem) {
                            code.loadWithoutSwitchingKind(x); // todo: this is stupid
                        }
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
                case lpar -> {
                    actPars(x.obj);

                    code.methodCall(x);

                    // pop unused return value, only necessary for non-void methods
                    if (x.type != Tab.noType) {
                        code.put(Code.OpCode.pop);
                    }
                }
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
        final Runnable ifStatement = () -> {
            check(if_);
            check(lpar);

            final var x = condition();
            code.fJump(x.op, x.fLabel);
            x.tLabel.here();

            check(rpar);

            statement(breakLabel);

            final var beyondLastStatement = new Label(code);

            if (sym == else_) {
                code.jump(beyondLastStatement);
                x.fLabel.here();

                check(else_);

                statement(breakLabel);
            } else {
                x.fLabel.here();
            }

            beyondLastStatement.here();
        };

        // "while" "(" Condition ")" Statement
        final Runnable whileStatement = () -> {
            check(while_);
            check(lpar);

            final var topLabel = new Label(code);
            topLabel.here();

            final var x = condition();
            code.fJump(x.op, x.fLabel);
            x.tLabel.here();

            check(rpar);

            statement(x.fLabel);

            code.jump(topLabel);
            x.fLabel.here();
        };

        // "break" ";"
        final Runnable breakStatement = () -> {
            check(break_);

            if (breakLabel == null) {
                error(NO_LOOP);
            } else {
                code.jump(breakLabel);
            }

            check(semicolon);
        };

        // "return" [ Expr ] ";"
        final Runnable returnStatement = () -> {
            check(return_);

            final var currentMethod = tab.find(currentMethodName);

            if (sym == semicolon) {
                if (currentMethod.type != Tab.noType) {
                    error(RETURN_NO_VAL);
                }
            } else {
                final var isVoidMethod = currentMethod.type == Tab.noType;
                if (isVoidMethod) {
                    error(RETURN_VOID);
                }

                final var x = expr();

                if (!isVoidMethod && !x.type.compatibleWith(currentMethod.type)) {
                    error(NON_MATCHING_RETURN_TYPE);
                }

                code.load(x);
            }

            code.put(Code.OpCode.exit);
            code.put(Code.OpCode.return_);

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
            () -> includes(firstDesignator, sym), designatorStatement,
            () -> sym == if_, ifStatement,
            () -> sym == while_, whileStatement,
            () -> sym == break_, breakStatement,
            () -> sym == return_, returnStatement,
            () -> sym == read, readStatement,
            () -> sym == print, printStatement,
            () -> sym == lbrace, () -> block(breakLabel),
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
    private Operand condition() {
        // CondTerm
        final var x = condTerm();

        // { "||" CondTerm }
        while (sym == or) {
            code.tJump(x.op, x.tLabel);

            check(or);

            x.fLabel.here();

            final var y = condTerm();
            x.fLabel = y.fLabel;
            x.op = y.op;
        }

        return x;
    }

    // CondFact { "&&" CondFact }.
    private Operand condTerm() {
        // CondFact
        final var x = condFact();

        // { "&&" CondFact }
        while (sym == and) {
            code.fJump(x.op, x.fLabel);

            check(and);

            final var y = condFact();
            x.op = y.op;
        }

        return x;
    }

    // Expr Relop Expr.
    private Operand condFact() {
        final var x = expr();
        final var condOp = relop();
        final var y = expr();

        code.loadAndIgnoreNull(x);
        code.loadAndIgnoreNull(y);

        if (x != null && y != null) {
            if (!x.type.compatibleWith(y.type)) {
                error(INCOMP_TYPES);
            }

            if (x.type.isRefType() && y.type.isRefType() && condOp != Code.CompOp.eq && condOp != Code.CompOp.ne) {
                error(EQ_CHECK);
            }
        }

        return new Operand(condOp, code);
    }

    // "==" | "!=" | ">" | ">=" | "<" | "<=".
    private Code.CompOp relop() {
        switch (sym) {
            case eql -> {
                check(eql);
                return Code.CompOp.eq;
            }
            case neq -> {
                check(neq);
                return Code.CompOp.ne;
            }
            case gtr -> {
                check(gtr);
                return Code.CompOp.gt;
            }
            case geq -> {
                check(geq);
                return Code.CompOp.ge;
            }
            case lss -> {
                check(lss);
                return Code.CompOp.lt;
            }
            case leq -> {
                check(leq);
                return Code.CompOp.le;
            }
            default -> {
                error(REL_OP);
                return Code.CompOp.eq;
            }
        }
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

                code.exponentiation(t.numVal);
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

                    // todo: i mean this kind of makes sense but what's the point of kind method then
                    x.kind = Operand.Kind.Stack;

                    actPars(x.obj);

                    code.methodCall(x);
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
    private void actPars(Obj method) {
        check(lpar);

        if (method == null) {
            error(NO_METH);
        }

        final var actualParams = new ArrayList<Operand>();

        if (includes(firstExpr, sym)) {
            final var x = expr();
            code.loadAndIgnoreNull(x);
            actualParams.add(x);

            while (sym == comma) {
                check(comma);

                final var y = expr();
                code.loadAndIgnoreNull(y);
                actualParams.add(y);
            }
        }

        if (method != null) {
            validateMethodCall(method, actualParams);
        }

        check(rpar);
    }

    /**
     * when wrapping one of the helpers, effectively turns it into { ... }
     */
    private void runUntilFalse(Supplier<Boolean> fn) {
        while (fn.get()) {}
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

    private void validateMethodCall(Obj method, List<Operand> actualParams) {
        if (actualParams.size() > method.nPars) {
            error(MORE_ACTUAL_PARAMS);
        } else if (actualParams.size() < method.nPars) {
            error(LESS_ACTUAL_PARAMS);
        } else {
            final var methodPars = getMethodParameters(method);
            for (var i = 0; i < actualParams.size(); i++) {
                final var o1 = actualParams.get(i);
                final var o2 = methodPars.get(i);

                if (o1 == null || o2 == null) {
                    continue;
                }

                if (!o1.type.assignableTo(o2.type)) {
                    error(PARAM_TYPE);
                }
            }
        }
    }

    private List<Obj> getMethodParameters(Obj method) {
        // the first `nPars` locals are parameters (this is terrible)
        // also, `values` does not guarantee insertion order, so this only works by accident :)
        return method.locals.values().stream().limit(method.nPars).toList();
    }
}
