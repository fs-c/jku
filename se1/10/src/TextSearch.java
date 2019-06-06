class Match {
	String target, slice;
	int col, row, matching;

	Match(int col, int row, int matching, String target, String slice) {
		this.col = col;
		this.row = row;
		this.matching = matching;

		this.target = target;
		this.slice = slice;
	}

	public void print() {
		Out.format("Found '%s' in row %d, column %d, %d/%d characters matched%n",
			slice, this.row, this.col, this.matching, target.length());
	}

	public static Match findBest(String haystack, String needle) {
		int col = 1;
		int row = 1;

		Match best = null;

		for (int i = 0; i < haystack.length() - needle.length(); i++, col++) {
			char current = haystack.charAt(i);

			if (current == '\n') {
				row++;
				col = 0;
			}

			String slice = Match.getSlice(haystack, i, needle.length());
			int matching = Match.getMatching(slice, needle);

			if (best == null || best.matching < matching)
				best = new Match(col, row, matching, needle, slice);
		}

		return best;
	}

	private static int getMatching(String source, String target) {
		int matching = 0;

		for (int j = 0; j < target.length(); j++)
			if (source.charAt(j) == target.charAt(j))
				matching++;
		
		return matching;
	}

	private static String getSlice(String source, int offset, int length) {
		return source.substring(offset, offset + length).toLowerCase();
	}
}

class TextSearch {
	public static void main(String[] args) {
		String fileName;

		if (args.length > 0) {
			fileName = args[0];
		} else {
			Out.print("File: ");
			fileName = In.readWord();
		}

		Out.print("Target: ");
		String target = (In.readLine()).toLowerCase();

		String file = readFile(fileName);
		Match best = Match.findBest(file, target);

		best.print();

		return;
	}

	public String readFile(String file) {
		In.open(file);

		String content = In.readFile();

		In.close();
	}
}