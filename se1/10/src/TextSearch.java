import java.awt.List;
import java.util.ArrayList;

class Match {
	int col, row, matching, searchLength;

	Match(int col, int row, int matching, int searchLength) {
		this.col = col;
		this.row = row;
		this.matching = matching;
		this.searchLength = searchLength;
	}

	public void print() {
		Out.format("Found in row %d, column %d, %d/%d characters matched",
			this.row, this.col, this.matching, this.searchLength);
	}
}

class TextSearch {
	public static void main(String[] args) {
		String file;

		if (args.length > 0) {
			file = args[0];
		} else {
			Out.print("File: ");
			file = In.readWord();
		}

		String target = (In.readLine()).toLowerCase();

		Out.format("searching for '%s' (%d)%n", target, target.length());			

		In.open(file);

		String slice = null;

		int col = 0;
		int row = 0;

		ArrayList<Match> matches = new ArrayList<Match>();

		while (In.done()) {
			col++;

			char current = In.read();

			if (current == '\n') {
				row++;
				col = 2;
			}

			int matching = 0;
			slice = buildSlice(slice, target.length(), current);

			for (int i = 0; i < slice.length(); i++) {
				if (slice.charAt(i) == target.charAt(i)) {
					matching++;
				} else break;
			}

			matches.add(new Match(col, row, matching, target.length()));

			Out.format("[%d / %d] (%d) - %s%n", col, row, matching, slice);
		}

		Match best = matches.get(0);

		for (Match m : matches)
			if (m.matching > best.matching)
				best = m;

		best.print();

		return;
	}

	static void printChars(char[] chars) {
		for (int i = 0; i < chars.length; i++) {
			Out.print(chars[i]);
		}

		Out.print('\n');
	}

	static String buildSlice(String prev, int max, char current) {
		String slice;

		if (prev == null)
			return "" + current;

		// If the old one is already full
		if (max <= prev.length()) {
			slice = prev.substring(1) + current;
		} else slice = prev + Character.toLowerCase(current);

		return slice;
	}
}
