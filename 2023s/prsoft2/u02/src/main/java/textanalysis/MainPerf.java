package textanalysis;

import inout.In;
import parallel.ParallelComputation;

import java.io.IOException;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;

public class MainPerf {

    public static void main(String[] args) throws IOException {

        In.open(Settings.fileName);
        String text = In.readFile();
        In.close();

        System.out.println("==========================================================");
        System.out.println("Text length = %d".formatted(text.length()));
        System.out.println("==========================================================");

        Settings.log = false;

        long start;
        long time;

        var problem = new TextProblem(text, 0, text.length());

        // warmup
        for (int i = 0; i < Settings.nWarmUpCycles; i++) {
            new ParallelComputation<AnalysisResult, TextProblem>().compute(problem);
        }

        // measuring
        // these settings performed best on my system
        Settings.threshold = 500;
        Settings.parallelism = 3;
        System.out.println("------------------------------------------------------------");
        System.out.println("THRESHHOLD: %,d".formatted(Settings.threshold));
        System.out.println("PARALLELISM: %,d".formatted(Settings.parallelism));
        System.out.println("------------------------------------------------------------");
        start = System.currentTimeMillis();
        for (int i = 0; i < Settings.nMeasureCycles; i++) {
            AnalysisResult result = new ParallelComputation<AnalysisResult, TextProblem>().compute(problem);
            result = null;
        }
        time = System.currentTimeMillis() - start;
        System.out.println("TIME = " + time);
        System.out.println("------------------------------------------------------------");



    }

}
