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
import java.util.function.Function;
import java.util.function.IntSupplier;

public class SmithCount {
    private static int[] getPrimeFactors(int n) {
        final ArrayList<Integer> primes = new ArrayList<Integer>();

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
        final List<Future<Integer>> promisedResults = new ArrayList<Future<Integer>>();

        final int shardSize = (to - from) / nrThreads;

        for (int i = 0; i < nrThreads; i++) {
            final int index = i;

            promisedResults.add(pool.submit(() -> (
                    seqCountSmith(from + (shardSize * index), from + (shardSize * (index + 1)))
            )));
        }

        final int missedSize = (to - from) - (shardSize * nrThreads);

        if (missedSize > 0) {
            promisedResults.add(pool.submit(() -> (
                    seqCountSmith(to - missedSize, to)
            )));
        }

        int count = 0;

        for (final Future<Integer> promise : promisedResults) {
            try {
                count += promise.get();
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            }
        }

        pool.shutdown();

        return count;
    }


    private static Duration getExecutionTime(final Runnable f) {
        Instant before = Instant.now();

        f.run();

        Instant after = Instant.now();

        return Duration.between(before, after);
    }

    private static void printComparisonBenchmark(final int from, final int to, final int threads) {
        System.out.format("benchmark from %d to %d with %d threads\n", from, to, threads);

        System.out.format("seq: %d ms\n", getExecutionTime(() -> seqCountSmith(from, to)).toMillis());
        System.out.format("par: %d ms\n", getExecutionTime(() -> parCountSmith(from, to, threads)).toMillis());
    }

    public static void main(String[] args) {
        printComparisonBenchmark(0, 100000, 4);
        printComparisonBenchmark(0, 100000, 16);
    }
}
