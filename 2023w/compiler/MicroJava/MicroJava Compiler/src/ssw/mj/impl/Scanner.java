package ssw.mj.impl;

import ssw.mj.Errors;
import ssw.mj.scanner.Token;

import java.io.IOException;
import java.io.PushbackReader;
import java.io.Reader;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.Function;

import static ssw.mj.Errors.Message.*;
import static ssw.mj.scanner.Token.Kind.*;

public class Scanner {

    // Scanner Skeleton - do not rename fields / methods !
    private static final char EOF = (char) -1;
    private static final char LF = '\n';
    private static final char CR = '\r';
    private static final char BACKSLASH = '\\';
    private static final char SINGLE_QUOTE = '\'';

    /**
     * Input data to read from.
     */
    private final PushbackReader in;

    /**
     * Lookahead character. (= next (unhandled) character in the input stream)
     */
    private char ch;

    /**
     * Current line in input stream.
     */
    private int line;

    /**
     * Current column in input stream.
     */
    private int col;

    /**
     * According errors object.
     */
    public final Errors errors;

    private boolean shouldIncreaseLineNum = false;

    public Scanner(Reader r) {
        // store reader
        in = new PushbackReader(r, 1);

        // initialize error handling support
        errors = new Errors();

        line = 1;
        col = 0;
        nextCh(); // read 1st char into ch, incr col to 1
    }

    /**
     * Adds error message to the list of errors.
     */
    public final void error(Token t, Errors.Message msg, Object... msgParams) {
        errors.error(t.line, t.col, msg, msgParams);

        // reset token content (consistent JUnit tests)
        t.numVal = 0;
        t.val = null;
    }

    /**
     * Mapping from keyword names to appropriate token codes.
     */
    private static final Map<String, Token.Kind> keywords;

    static {
        keywords = new HashMap<>();

        keywords.put("break", break_);
        keywords.put("class", class_);
        keywords.put("else", else_);
        keywords.put("final", final_);
        keywords.put("if", if_);
        keywords.put("new", new_);
        keywords.put("print", print);
        keywords.put("program", program);
        keywords.put("read", read);
        keywords.put("return", return_);
        keywords.put("void", void_);
        keywords.put("while", while_);
    }

    /**
     * Returns next token. To be used by parser.
     */
    public Token next() {
        while (Character.isWhitespace(this.ch)) {
            this.nextCh();
        }

        // identifier, keyword, number, char constant
        if (this.isLetter(this.ch)) {
            return this.readName();
        } else if (this.isDigit(this.ch)) {
            return this.readNumber();
        } else if (this.ch == SINGLE_QUOTE) {
            return this.readCharConstant();
        }

        Token token = new Token(none, this.line, this.col);

        switch (this.ch) {
            // could be +, ++ or +=
            case '+' -> nextOptionalsOrDefault(token, Map.of('+', pplus, '=', plusas), plus);
            // could be -, -- or -=
            case '-' -> nextOptionalsOrDefault(token, Map.of('-', mminus, '=', minusas), minus);
            // could be *, ** or *=
            case '*' -> nextOptionalsOrDefault(token, Map.of('*', exp, '=', timesas), times);
            // could be % or %=
            case '%' -> nextOptionalsOrDefault(token, Map.of('=', remas), rem);
            // could be = or ==
            case '=' -> nextOptionalsOrDefault(token, Map.of('=', eql), assign);
            // could be < or <=
            case '<' -> nextOptionalsOrDefault(token, Map.of('=', leq), lss);
            // could be > or >=
            case '>' -> nextOptionalsOrDefault(token, Map.of('=', geq), gtr);
            // these are only valid in their expanded form
            case '!' -> nextExactOrError(token, '=', neq);
            case '&' -> nextExactOrError(token, '&', and);
            case '|' -> nextExactOrError(token, '|', or);
            // could be /, /= or /*
            case '/' -> {
                final var next = this.peekCh();
                if (next == '=') {
                    this.nextCh();
                    token.kind = slashas;
                } else if (next == '*') {
                    this.nextCh();
                    this.skipComment();
                    return this.next();
                } else {
                    token.kind = slash;
                }
            }
            // no ambiguity
            case '(' -> token.kind = lpar;
            case ')' -> token.kind = rpar;
            case '[' -> token.kind = lbrack;
            case ']' -> token.kind = rbrack;
            case '{' -> token.kind = lbrace;
            case '}' -> token.kind = rbrace;
            case ';' -> token.kind = semicolon;
            case ',' -> token.kind = comma;
            case '.' -> token.kind = period;
            case EOF -> token.kind = eof;
            default -> this.error(token, INVALID_CHAR, this.ch);
        }

        this.nextCh();


        return token;
    }

    private void nextOptionalsOrDefault(Token token, Map<Character, Token.Kind> options, Token.Kind defaultKind) {
        final var next = this.peekCh();
        if (options.containsKey(next)) {
            this.nextCh();
            token.kind = options.get(next);
        } else {
            token.kind = defaultKind;
        }
    }

    private void nextExactOrError(Token token, char expected, Token.Kind kind) {
        final var next = this.peekCh();
        if (next == expected) {
            this.nextCh();
            token.kind = kind;
        } else {
            this.error(token, INVALID_CHAR, this.ch);
        }
    }

    /**
     * Reads next character from input stream into ch. Keeps pos, line and col
     * in sync with reading position.
     */
    private void nextCh() {
        // this is a bit of a hack, but it makes sure that col numbers are correct if we happen
        // to try reading beyond eof (which shouldn't happen but eh)
        if (this.ch == EOF) {
            return;
        }

        if (shouldIncreaseLineNum) {
            this.line++;
            this.shouldIncreaseLineNum = false;
        }

        try {
            final var next = (char)this.in.read();

            if (next == CR) {
                nextCh();
                return;
            }

            if (next == LF) {
                this.shouldIncreaseLineNum = true;
                this.col = 0;
                this.ch = ' ';
                return;
            }

            this.col++;
            this.ch = next;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Reads next character from input stream without changing instance state.
     */
    private char peekCh() {
        try {
            final var next = (char) this.in.read();
            this.in.unread(next);
            return next;
        } catch (IOException e) {
            // we are just peeking, act like nothing happened -- when we read the char for real we will have
            // proper error handling with correct state
            return '\0';
        }
    }

    /**
     * Reads a string from the input stream until the condition is not satisfied anymore.
     */
    private String readString(Function<Character, Boolean> condition) {
        final var builder = new StringBuilder();

        // we assume that the first char has already been read and satisfies the condition
        do {
            builder.append(this.ch);

            this.nextCh();
        } while (condition.apply(this.ch));

        return builder.toString();
    }

    private Token readName() {
        final var startingCol = this.col;
        final var string = this.readString((ch) -> this.isLetter(ch) || this.isDigit(ch) || ch == '_');

        if (keywords.containsKey(string)) {
            return new Token(keywords.get(string), line, startingCol);
        } else {
            final var token = new Token(ident, this.line, startingCol);
            token.val = string;

            return token;
        }
    }

    private Token readNumber() {
        final var token = new Token(number, this.line, this.col);
        final var string = this.readString(this::isDigit);

        try {
            token.val = string;
            token.numVal = Integer.parseInt(string);
        } catch (NumberFormatException e) {
            error(token, BIG_NUM, string);
        }

        return token;
    }

    private Token readCharConstant() {
        final var token = new Token(charConst, this.line, this.col);

        // special case for newline right after opening quote: we need to peek here because otherwise nextCh()
        // would skip the newline, and we wouldn't know that it was there
        final var peeked = this.peekCh();
        if (this.isNewline(peeked)) {
            this.nextCh();
            error(token, ILLEGAL_LINE_END);
            return token;
        }

        // we assume that we just read the opening single quote, this is the first character of the constant
        this.nextCh();

        if (this.ch == BACKSLASH) {
            this.nextCh();

            final BiConsumer<Character, String> applyEscapedValue = (escaped, readable) -> {
                token.numVal = escaped;
                token.val = "\\" + readable;
            };

            switch (this.ch) {
                case 'r' -> applyEscapedValue.accept('\r', "r");
                case 'n' -> applyEscapedValue.accept('\n', "n");
                case '\'' -> applyEscapedValue.accept('\'', "'");
                case '\\' -> applyEscapedValue.accept('\\', "\\");
                default -> error(token, UNDEFINED_ESCAPE, this.ch);
            }
        } else if (this.ch == SINGLE_QUOTE) {
            error(token, EMPTY_CHARCONST);
            this.nextCh();
            return token;
        } else if (this.isNewline(this.ch)) {
            error(token, ILLEGAL_LINE_END);
        } else {
            token.numVal = this.ch;
        }

        // consume the closing single quote
        this.nextCh();
        if (ch != SINGLE_QUOTE) {
            if (this.ch == EOF) {
                // we only want the eof error if it comes right after the last content or after the opening quote,
                // i.e. if the last character the regular logic expected to be a normal one was in fact eof
                if (token.numVal == EOF) {
                    error(token, EOF_IN_CHAR);
                } else {
                    // ...otherwise there would have been space for the quote before the eof, in which case the
                    // regular missing quote error is fine
                    error(token, MISSING_QUOTE);
                }
            } else {
                error(token, MISSING_QUOTE);
            }

            return token;
        }

        // read the next char because next() expects it, but not if we errored out
        this.nextCh();

        return token;
    }

    private boolean isNewline(char c) {
        return c == CR || c == LF;
    }

    void skipComment() {
        // starting col minus one because we assume that we just read the opening slash and star, but we want it
        // to be the col of the slash
        final var startingCol = this.col - 1;

        // discard star
        this.nextCh();

        int openComments = 1;
        var next = this.peekCh();

        while (next != EOF) {
            if (this.ch == '/' && next == '*') {
                this.nextCh();
                openComments++;
            }

            if (this.ch == '*' && next == '/') {
                this.nextCh();
                openComments--;
            }

            if (openComments == 0) {
                this.nextCh();
                return;
            }

            this.nextCh();
            next = this.peekCh();
        }

        // we are checking if the peeked char is eof, need to actually read it so next() knows what's up
        this.nextCh();
        this.error(new Token(none, this.line, startingCol), EOF_IN_COMMENT);
    }

    private boolean isLetter(char c) {
        return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
    }

    private boolean isDigit(char c) {
        return ('0' <= c) && (c <= '9');
    }

    // ================================================
    // ================================================
}
