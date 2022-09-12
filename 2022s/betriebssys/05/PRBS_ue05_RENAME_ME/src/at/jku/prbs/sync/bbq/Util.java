package at.jku.prbs.sync.bbq;

public class Util {

	/**
	 * Prints the message in either the first or the second column.
	 * Flushes the output buffer to make sure that the message is printed soon.
	 */
	public static void log(String message, boolean secondColumn) {
		System.out.println((secondColumn ? "\t\t\t\t\t\t\t" : "" ) + message);
		System.out.flush();
	}
	
}
