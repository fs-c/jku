package textanalysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class AnalysisResult {
    static public AnalysisResult combine(AnalysisResult r1, AnalysisResult r2) {
        var result = new AnalysisResult();

        result.wordCount = r1.wordCount + r2.wordCount;

        result.sortedWords = new ArrayList<>();
        result.sortedWords.addAll(r1.sortedWords);
        result.sortedWords.addAll(r2.sortedWords);
        Collections.sort(result.sortedWords);

        result.shortestWord = Math.min(r1.shortestWord, r2.shortestWord);
        result.longestWord = Math.max(r1.longestWord, r2.longestWord);

        return result;
    }

    private int wordCount = 0;
    private List<String> sortedWords = new ArrayList<String>();
    private int shortestWord = Integer.MAX_VALUE;
    private int longestWord = 0;

    public void handleWord(String word) {
        wordCount++;

        sortedWords.add(word);
        // todo: this is terrible
        Collections.sort(sortedWords);

        var length = word.length();
        if (length < shortestWord) {
            shortestWord = length;
        } else if (length > longestWord) {
            longestWord = length;
        }
    }

    @Override
    public String toString() {
        return "AnalysisResult{" +
                "wordCount=" + wordCount +
                ", sortedWords=" + sortedWords +
                ", shortestWord=" + shortestWord +
                ", longestWord=" + longestWord +
                '}';
    }
}
