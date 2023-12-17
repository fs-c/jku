package ssw.mj.impl;

import ssw.mj.symtab.Obj;
import ssw.mj.symtab.Scope;
import ssw.mj.symtab.Struct;

import java.util.Objects;

import static ssw.mj.Errors.Message.*;

public final class Tab {

    // Universe
    public static final Struct noType = new Struct(Struct.Kind.None);
    public static final Struct intType = new Struct(Struct.Kind.Int);
    public static final Struct charType = new Struct(Struct.Kind.Char);
    public static final Struct nullType = new Struct(Struct.Kind.Class);

    public final Obj noObj, chrObj, ordObj, lenObj;

    /**
     * Only used for reporting errors.
     */
    private final Parser parser;
    /**
     * The current top scope.
     */
    public Scope curScope = null;
    // First scope opening (universe) will increase this to -1
    /**
     * Nesting level of current scope.
     */
    private int curLevel = -2;

    public Tab(Parser p) {
        parser = p;
        noObj = new Obj(Obj.Kind.Var, "$none", intType);
        noObj.val = 0;
        noObj.adr = 0;
        noObj.level = 0;
        noObj.nPars = 0;
        noObj.locals = null;

        // opening scope (curLevel goes to -1, which is the universe level)
        openScope();

        insert(Obj.Kind.Type, "int", intType);
        insert(Obj.Kind.Type, "char", charType);
        insert(Obj.Kind.Con, "null", nullType);

        chrObj = insert(Obj.Kind.Meth, "chr", charType);
        openScope();
        insert(Obj.Kind.Var, "i", intType, 1);
        chrObj.locals = curScope.locals();
        chrObj.nPars = curScope.nVars();
        closeScope();

        ordObj = insert(Obj.Kind.Meth, "ord", intType);
        openScope();
        insert(Obj.Kind.Var, "ch", charType, 1);
        ordObj.locals = curScope.locals();
        ordObj.nPars = curScope.nVars();
        closeScope();

        lenObj = insert(Obj.Kind.Meth, "len", intType);
        openScope();
        insert(Obj.Kind.Var, "arr", new Struct(noType), 1);
        lenObj.locals = curScope.locals();
        lenObj.nPars = curScope.nVars();
        closeScope();
    }

    public void openScope() {
        curScope = new Scope(curScope);
        curLevel++;
    }

    public void closeScope() {
        curScope = curScope.outer();
        curLevel--;
    }

    public Obj insert(Obj.Kind kind, String name, Struct type, int level) {
        if (curScope.findLocal(name) != null) {
            parser.error(DECL_NAME, name);
        }

        final var obj = new Obj(kind, name, type);
        if (kind == Obj.Kind.Var) {
            obj.level = level;
            obj.adr = curScope.nVars();
        }

        curScope.insert(obj);
        return obj;
    }

    public Obj insert(Obj.Kind kind, String name, Struct type) {
        return insert(kind, name, type, curLevel);
    }

    /**
     * Retrieves the object with <code>name</code> from the innermost scope.
     */
    public Obj find(String name) {
        final var result = curScope.findGlobal(name);

        if (result == null) {
            parser.error(NOT_FOUND, name);
        }

        return Objects.requireNonNullElse(result, noObj);
    }

    /**
     * Retrieves the field <code>name</code> from the fields of
     * <code>type</code>.
     */
    public Obj findField(String name, Struct type) {
        final var result = type.fields.get(name);

        if (result == null) {
            parser.error(NO_FIELD, name);
        }

        return result;
    }

    // ===============================================
    // ===============================================
}
