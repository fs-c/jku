package textanalysis;

import inout.In;
import parallel.ParallelComputation;

import java.io.IOException;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;

public class Main {

    public static void main(String[] args) throws IOException {

        In.open(Settings.fileName);
        String text = In.readFile();
        In.close();

        System.out.println("==========================================================");
        System.out.println("Text length = %d".formatted(text.length()));
        System.out.println("==========================================================");

        Settings.log = true;

        Settings.threshold = 1_000;
        System.out.println("------------------------------------------------------------");
        System.out.println("THRESHHOLD: %,d".formatted(Settings.threshold));
        System.out.println("------------------------------------------------------------");

        var problem = new TextProblem(text, 0, text.length());
        var result = new ParallelComputation<AnalysisResult, TextProblem>().compute(problem);

        System.out.println(result);
        System.out.println("------------------------------------------------------------");
    }

}
