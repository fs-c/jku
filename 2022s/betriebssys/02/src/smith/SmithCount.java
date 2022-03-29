package smith;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

public class SmithCount {
    private static int[] getPrimeFactors(int n) {
        final ArrayList<Integer> primes = new ArrayList<>();

        int factor = 2;
        while (n > 1) {
            if (n % factor == 0) {
                primes.add(factor);
                n /= factor;
            } else {
                factor++;
            }
        }

        return primes.stream().mapToInt(Integer::valueOf).toArray();
    }

    private static int getSumOfDigits(int n) {
        int sum = 0;

        while (n != 0) {
            sum += n % 10;
            n /= 10;
        }

        return sum;
    }

    private static boolean isSmithNumber(final int n) {
        final int[] factors = getPrimeFactors(n);

        // Prime numbers and zero aren't smith numbers
        if (factors.length <= 1) {
            return false;
        }

        final int sumOfDigits = getSumOfDigits(n);
        final int sumOfPrimeDigits = Arrays.stream(factors)
                .reduce(0, (acc, cur) -> acc + getSumOfDigits(cur));

        return sumOfDigits == sumOfPrimeDigits;
    }

    public static int seqCountSmith(final int from, final int to) {
        int count = 0;

        for (int i = from; i <= to; i++) {
            if (isSmithNumber(i)) {
                count++;
            }
        }

        return count;
    }

    public static int parCountSmith(final int from, final int to, final int nrThreads) {
        final ExecutorService pool = Executors.newFixedThreadPool(nrThreads);
        final List<Future<Integer>> promisedResults = new ArrayList<>();

        final int subsetSize = (to - from) / nrThreads;

        for (int i = 0; i < nrThreads; i++) {
            final int index = i;

            promisedResults.add(pool.submit(() -> (
                    seqCountSmith(from + (subsetSize * index), from + (subsetSize * (index + 1)))
            )));
        }

        final int missedSize = (to - from) - (subsetSize * nrThreads);

        if (missedSize > 0) {
            promisedResults.add(pool.submit(() -> (
                    seqCountSmith(to - missedSize, to)
            )));
        }

        return promisedResults.stream().mapToInt(promise -> {
                try {
                    return promise.get();
                } catch (InterruptedException | ExecutionException e) {
                    e.printStackTrace();

                    return 0;
                }
        }).sum();
    }

    private static Duration getExecutionTime(final Runnable f) {
        final Instant before = Instant.now();

        f.run();

        final Instant after = Instant.now();

        return Duration.between(before, after);
    }

    private static void printComparisonBenchmark(final int from, final int to, final int threads) {
        System.out.format("benchmark from %d to %d\n", from, to);

        System.out.format("seq: %d ms\n",
                getExecutionTime(() -> seqCountSmith(from, to)).toMillis());
        System.out.format("par: %d ms (%d threads)\n",
                getExecutionTime(() -> parCountSmith(from, to, threads)).toMillis(), threads);
    }

    public static void main(String[] args) {
        printComparisonBenchmark(0, 100000, 4);
        printComparisonBenchmark(0, 100000, 16);
    }
}
