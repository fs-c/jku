package textanalysis;

import parallel.Pair;
import parallel.Problem;

public class TextProblem implements Problem<AnalysisResult, TextProblem> {
    private String text;
    private int from;
    private int to;

    TextProblem(String text, int from, int to) {
        this.text = text;
        this.from = from;
        this.to = to;
    }

    @Override
    public boolean isSmall() {
        return (to - from) < Settings.threshold;
    }

    @Override
    public Pair<TextProblem, TextProblem> split() {
        int pivot = from + (to - from) / 2;

        while (Character.isLetter(text.charAt(pivot))) {
            pivot++;
        }

        if (Settings.log) {
            System.out.format("splitting [%d, %d] into [[%d, %d], [%d, %d]]\n", from, to, from, pivot, pivot + 1, to);
        }

        return new Pair<>(new TextProblem(text, from, pivot), new TextProblem(text, pivot + 1, to));
    }

    @Override
    public AnalysisResult combine(AnalysisResult result1, AnalysisResult result2) {
        return AnalysisResult.combine(result1, result2);
    }

    @Override
    public AnalysisResult solveSequential() {
        if (Settings.log) {
            System.out.format("solving [%d, %d] sequentially\n", from, to);
        }

        var analysisResult = new AnalysisResult();

        boolean inWord = false;
        int wordBegin = -1;

        for (int i = from; i < to; i++) {
            char c = text.charAt(i);
            boolean isLetter = Character.isLetter(c);

            if (isLetter && !inWord) {
                inWord = true;
                wordBegin = i;
            }

            if (!isLetter && inWord) {
                inWord = false;
                analysisResult.handleWord(text.substring(wordBegin, i));
            }
        }

        return analysisResult;
    }
}
