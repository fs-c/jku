package ssw.mj.impl;

import ssw.mj.codegen.Label;
import ssw.mj.codegen.Operand;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;

import static ssw.mj.Errors.Message.*;

public final class Code {

    public enum OpCode {
        load,
        load_0,
        load_1,
        load_2,
        load_3,
        store,
        store_0,
        store_1,
        store_2,
        store_3,
        getstatic,
        putstatic,
        getfield,
        putfield,
        const_0,
        const_1,
        const_2,
        const_3,
        const_4,
        const_5,
        const_m1,
        const_,
        add,
        sub,
        mul,
        div,
        rem,
        neg,
        shl,
        shr,
        inc,
        new_,
        newarray,
        aload,
        astore,
        baload,
        bastore,
        arraylength,
        pop,
        dup,
        dup2,
        jmp,
        jeq,
        jne,
        jlt,
        jle,
        jgt,
        jge,
        call,
        return_,
        enter,
        exit,
        read,
        print,
        bread,
        bprint,
        trap,
        nop;

        public int code() {
            return ordinal() + 1;
        }

        public String cleanName() {
            String name = name();
            if (name.endsWith("_")) {
                name = name.substring(0, name.length() - 1);
            }
            return name;
        }

        public static OpCode get(int code) {
            if (code < 1 || code > values().length) {
                return null;
            }
            return values()[code - 1];
        }
    }

    public enum CompOp {
        eq, ne, lt, le, gt, ge;

        public static CompOp invert(CompOp op) {
            if (op == null) {
                throw new IllegalArgumentException("Compare operator must not be null!");
            }
            switch (op) {
                case eq:
                    return ne;
                case ne:
                    return eq;
                case lt:
                    return ge;
                case le:
                    return gt;
                case gt:
                    return le;
                case ge:
                    return lt;
                default:
                    // Cannot happen, we covered all six compare operations as well as null parameter
                    // This is purely to prevent the compiler from complaining about a missing return statement
                    throw new IllegalArgumentException("Impossible compare operator");
            }
        }

        public static OpCode toOpCode(CompOp op) {
            switch (op) {
                case eq:
                    return OpCode.jeq;
                case ge:
                    return OpCode.jge;
                case gt:
                    return OpCode.jgt;
                case le:
                    return OpCode.jle;
                case lt:
                    return OpCode.jlt;
                case ne:
                    return OpCode.jne;
            }
            return OpCode.nop;
        }
    }

    /**
     * Code buffer
     */
    public byte[] buf;

    /**
     * Program counter. Indicates next free byte in code buffer.
     */
    public int pc;

    /**
     * PC of main method (set by parser).
     */
    public int mainpc;

    /**
     * Length of static data in words (set by parser).
     */
    public int dataSize;

    /**
     * According parser.
     */
    private final Parser parser;

    private final Tab tab;

    // ----- initialization

    public Code(Parser p, Tab t) {
        parser = p;
        tab = t;
        buf = new byte[100];
        pc = 0;
        mainpc = -1;
        dataSize = 0;
    }

    // ----- code storage management

    public void put(OpCode code) {
        put(code.code());
    }

    public void put(int x) {
        if (pc == buf.length) {
            buf = Arrays.copyOf(buf, buf.length * 2);
        }
        buf[pc++] = (byte) x;
    }

    public void put2(int x) {
        put(x >> 8);
        put(x);
    }

    public void put4(int x) {
        put2(x >> 16);
        put2(x);
    }

    public void put2(int pos, int x) {
        int oldpc = pc;
        pc = pos;
        put2(x);
        pc = oldpc;
    }

    public int get(int pos) {
        return buf[pos];
    }

    /**
     * Write the code buffer to the output stream.
     */
    public void write(OutputStream os) throws IOException {
        int codeSize = pc;

        ByteArrayOutputStream header = new ByteArrayOutputStream();
        DataOutputStream headerWriter = new DataOutputStream(header);
        headerWriter.writeByte('M');
        headerWriter.writeByte('J');
        headerWriter.writeInt(codeSize);
        headerWriter.writeInt(dataSize);
        headerWriter.writeInt(mainpc);
        headerWriter.close();

        os.write(header.toByteArray());

        os.write(buf, 0, codeSize);
        os.flush();
        os.close();
    }

    /**
     * Load the operand x onto the expression stack.
     */
    public void load(Operand x) {
        switch (x.kind) {
            case Con -> loadConst(x.val);
            case Static -> {
                put(OpCode.getstatic);
                put2(x.adr);
            }
            case Local -> {
                if (x.adr >= 0 && x.adr <= 3) {
                    put(OpCode.load_0.code() + x.adr);
                } else {
                    put(OpCode.load);
                    put(x.adr);
                }
            }
            case Fld -> {
                put(OpCode.getfield);
                put2(x.adr);

            }
            case Elem -> {
                if (x.type == Tab.charType) {
                    put(OpCode.baload);
                } else {
                    put(OpCode.aload);
                }
            }
            case Stack -> {
                // Nothing to do, already loaded
            }
            default -> parser.error(NO_VAL);
        }

        x.kind = Operand.Kind.Stack;
    }

    public void loadAndIgnoreNull(Operand x) {
        if (x != null) {
            load(x);
        }
    }

    /**
     * Generate an increment instruction that increments x by n.
     */
    public void inc(Operand x, int n) {
        switch (x.kind) {
            case Local -> {
                put(OpCode.inc);
                put(x.adr);
                put(n);
            }
            case Static -> {
                load(x);
                loadConst(n);
                put(OpCode.add);
                put(OpCode.putstatic);
                put2(x.adr);
            }
            case Elem, Fld -> {
                loadConst(n);
                put(OpCode.add);
                assign(x, null);
            }
            default -> parser.error(CANNOT_ASSIGN_TO, x.kind);
        }
    }

    /**
     * Generate an assignment x = y.
     */
    public void assign(Operand x, Operand y) {
        if (y != null) {
            load(y);
        }

        switch (x.kind) {
            case Local -> {
                if (x.adr >= 0 && x.adr <= 3) {
                    put(OpCode.store_0.code() + x.adr);
                } else {
                    put(OpCode.store);
                    put(x.adr);
                }
            }
            case Fld -> {
                put(OpCode.putfield);
                put2(x.adr);
            }
            case Static -> {
                put(OpCode.putstatic);
                put2(x.adr);
            }
            case Elem -> {
                if (x.type == Tab.charType) {
                    put(OpCode.bastore);
                } else {
                    put(OpCode.astore);
                }
            }
            default -> parser.error(CANNOT_ASSIGN_TO, x.kind);
        }
    }

    /**
     * Load an integer constant onto the expression stack.
     */
    public void loadConst(int n) {
        if (n >= 0 && n <= 5) {
            put(OpCode.const_0.code() + n);
        } else if (n == -1) {
            put(OpCode.const_m1);
        } else {
            put(OpCode.const_);
            put4(n);
        }
    }

    /**
     * Prepares a compound assignment.
     */
    public void compoundAssignmentPrepare(Operand x) {
        if (x.kind != Operand.Kind.Fld && x.kind != Operand.Kind.Elem) {
            return;
        }

        switch (x.kind) {
            case Fld -> put(OpCode.dup);
            case Elem -> put(OpCode.dup2);
        }

        loadWithoutSwitchingKind(x);
    }

    public void loadWithoutSwitchingKind(Operand x) {
        final var kindBeforeLoad = x.kind;

        load(x);

        x.kind = kindBeforeLoad;
    }

    // --------------------

    public void exponentiation(int exponent) {
        if (exponent == 0) {
            put(Code.OpCode.pop);
            loadConst(1);
        } else if (exponent != 1) {
            final var endLabel = new Label(this);
            final var baseIsTwoLabel = new Label(this);

            // check base == 2
            put(OpCode.dup);
            loadConst(2);
            tJump(CompOp.eq, baseIsTwoLabel);

            // code block for base != 2
            for (var i = 0; i < exponent - 1; i++) {
                put(Code.OpCode.dup);
            }

            for (var i = 0; i < exponent - 1; i++) {
                put(Code.OpCode.mul);
            }

            jump(endLabel);

            // code block for base == 2
            baseIsTwoLabel.here();
            loadConst(exponent - 1);
            put(OpCode.shl);

            endLabel.here();
        }
    }

    public void methodCall(Operand x) {
        if (x.obj == tab.ordObj || x.obj == tab.chrObj) {
            // just type conversions, no need to do anything
        } else if (x.obj == tab.lenObj) {
            put(OpCode.arraylength);
        } else {
            final var relativeTarget = x.adr - pc;

            put(OpCode.call);
            put2(relativeTarget);
        }
    }

    /**
     * Unconditional jump.
     */
    public void jump(Label lab) {
        put(OpCode.jmp);
        lab.put();
    }

    /**
     * True Jump. Generates conditional jump instruction and links it to true
     * jump chain.
     */
    public void tJump(CompOp op, Label to) {
        put(CompOp.toOpCode(op));
        to.put();
    }

    /**
     * False Jump. Generates conditional jump instruction and links it to false
     * jump chain.
     */
    public void fJump(CompOp op, Label to) {
        put(CompOp.toOpCode(CompOp.invert(op)));
        to.put();
    }
}
