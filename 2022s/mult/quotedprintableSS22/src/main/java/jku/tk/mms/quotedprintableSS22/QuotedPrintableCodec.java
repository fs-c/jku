package jku.tk.mms.quotedprintableSS22;

import java.util.Locale;

public class QuotedPrintableCodec {
	public static final char DEFAULT_QUOTE_CHAR	= '=';

	private final char quoteChar;

	public QuotedPrintableCodec() {
		this(DEFAULT_QUOTE_CHAR);
	}
	
	public QuotedPrintableCodec(char quoteChar) {
		this.quoteChar = quoteChar;
	}

	private boolean shouldEscape(char c) {
		return !(c == 9 || (c >= 32 && c <= 60) || (c >= 62 && c <= 126));
	}
	
	public String encode(String plain) {
		StringBuilder quoted = new StringBuilder();
		
		for (char c : plain.toCharArray()) {
			if (shouldEscape(c)) {
				quoted.append(quoteChar).append(Integer.toHexString(c).toUpperCase());
			} else {
				quoted.append(c);
			}
		}

		return quoted.toString();
	}
	
	public String decode(String quoted) {
		StringBuilder plain = new StringBuilder();

		for (int i = 0; i < quoted.length(); i++) {
			char c = quoted.charAt(i);

			if (c == quoteChar) {
				String hex = String.valueOf(quoted.charAt(++i)) +
						quoted.charAt(++i);

				plain.append((char)Integer.decode("0x" + hex).intValue());
			} else {
				plain.append(c);
			}
		}

		return plain.toString();
	}
}
