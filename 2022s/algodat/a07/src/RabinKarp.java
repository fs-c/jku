
import java.util.ArrayList;

public class RabinKarp {
	/**
	 * This method uses the RabinKarp algorithm to search a given pattern in a given input text. 
	 * 
	 * @param pattern - The pattern that is searched in the text.
	 * @param text - The text in which the pattern is searched.
	 * @return An ArrayList<Integer> containing the start indices of the found patterns in the input text.
	 * @throws IllegalArgumentException if pattern or text is null.
	 */
	static public ArrayList<Integer> search(String pattern, String text) throws IllegalArgumentException {
		if (pattern == null || text == null || pattern.length() == 0) {
			throw new IllegalArgumentException();
		}

		ArrayList<Integer> result = new ArrayList<Integer>();

		if (text.length() == 0 || pattern.length() > text.length()) {
			return result;
		}

		long patternHash = getRollingHashValue(pattern.toCharArray(), '0', -1);
		long textHash = -1;

		for (int i = 0; i < text.length() - pattern.length(); i++) {
			String sequence = text.substring(i, i + pattern.length());

			textHash = getRollingHashValue(sequence.toCharArray(), i > 0 ? text.charAt(i - 1) : '0', textHash);

			if (patternHash == textHash && sequence.equals(pattern)) {
				result.add(i);
			}
		}

		return result;
	}

		
	/**
	 * This method calculates the (rolling) hash code for a given character sequence. For the calculation
	 * use the base as given in the assignment sheet.
	 * If previousHash has the value -1, the rolling hash code shall be initialized with
	 * the characters given in the sequence. This can also be used to calculate the hashcode for the pattern!
	 * 
	 * @param sequence - The char sequence for which the (rolling) hash shall be computed.
	 * @param lastCharacter - The character that shall be removed from the hash.  
	 * @param previousHash - The previously calculated hash value that will be reused for the new hash values.
	 *                       A previousHash value of -1 indicates the initialization of the rolling hash code. 
	 * @return calculated hash value for the given character sequence.
	 */
	static public long getRollingHashValue(char[] sequence, char lastCharacter, long previousHash) {
		final int base = 29;

		long hash = 0;

		if (previousHash == -1) {
			for (int i = 0; i < sequence.length; i++) {
				hash += sequence[i] * Math.pow(base, sequence.length - i - 1);
			}
		} else {
			hash = (previousHash * base)
					- (lastCharacter * (long)Math.pow(base, sequence.length))
					+ sequence[sequence.length - 1];
		}

		return hash;
    }

	public static void main(String[] args) {
		var result = getRollingHashValue("ef".toCharArray(), 'a', -1);

		System.out.format("hash: %d", result);
	}
}
