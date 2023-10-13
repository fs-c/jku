package org.jku.ssw.prsw2.ue9;

import java.util.Arrays;
import java.util.Random;
import java.util.concurrent.TimeUnit;
import java.util.stream.IntStream;

import org.jku.ssw.prsw2.ue9.common.NoAdvancedSolutionException;
import org.jku.ssw.prsw2.ue9.jni.AdvancedJNISorter;
import org.jku.ssw.prsw2.ue9.jni.JNISorter;
import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Fork;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Measurement;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.OutputTimeUnit;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.TearDown;
import org.openjdk.jmh.annotations.Warmup;

/**
 * Simple JMH based implementation of a sorting benchmark testing different
 * sorting implementations.
 *
 */
public class SortingBenchmark {
	public static void main(String[] args) throws Exception {
		org.openjdk.jmh.Main.main(args);
	}

	/**
	 * Number of benchmark iterations taken for result measurement.
	 */
	private static final int MEASUREMENT_ITERATIONS = 5;
	/**
	 * Number of benchmark iterations taken for code warmup.
	 */
	private static final int WARMUP_ITERATIONS = 10;

	/**
	 * Workload for the sorting benchmark. Initialized once per benchmark thread,
	 * re-set before every benchmark call.
	 */
	@State(Scope.Thread)
	public static class SortingWorkload {
		/**
		 * Default seed for sorting random number generator. FIXME use your student ID
		 * as a seed.
		 */
		public static final long DEFAULT_SEED = 11804751;
		/**
		 * Number of arrays to sort.
		 */
		public static final int DEFAULT_D1 = 100_000;
		/**
		 * Number of elements per array to sort.
		 */
		public static final int DEFAULT_D2 = 80;
		/**
		 * Arrays to sort.
		 */
		private final int[][] content;

		/**
		 * Called by generated benchmark harness to create the workload.
		 */
		public SortingWorkload() {
			this(DEFAULT_D1, DEFAULT_D2, DEFAULT_SEED);
		}

		public SortingWorkload(int d1, int d2, long seed) {
			content = new int[d1][];
			for (int i = 0; i < d1; i++) {
				content[i] = new int[d2];
			}
			fill(seed);
		}

		public SortingWorkload(int[][] content) {
			this.content = content;
		}

		public int[][] getContent() {
			return content;
		}

		/**
		 * Check that the array is sorted ascending.
		 */
		public boolean sorted() {
			return Arrays.stream(content)
					.allMatch(arr -> IntStream.range(1, arr.length).allMatch(j -> arr[j - 1] <= arr[j]));
		}

		/**
		 * Fill the array with random integers computed with the given seed.
		 */
		private void fill(long seed) {
			Random r = new Random(seed);
			for (int i = 0; i < content.length; i++) {
				for (int j = 0; j < content[i].length; j++) {
					content[i][j] = r.nextInt();
				}
			}
		}

		/**
		 * Re-set the content array with the default seed values.
		 */
		@Setup(Level.Invocation)
		public void setup() {
			fill(DEFAULT_SEED);
		}

		/**
		 * Check the array is sorted after every benchmark invocation.
		 */
		@TearDown(Level.Invocation)
		public void teardown() {
			if (!sorted()) {
				throw new RuntimeException("Array not sorted properly...");
			}
		}

	}

	/**
	 * Sort benchmark with implementation in JNI.
	 */
	@Benchmark
	@Fork(1)
	@BenchmarkMode(Mode.AverageTime)
	@OutputTimeUnit(TimeUnit.MILLISECONDS)
	@Warmup(iterations = WARMUP_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	@Measurement(iterations = MEASUREMENT_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	public void jnisort(SortingWorkload workload) {
		// nothing to do here - please take a look into the JNISorter class instead.
		JNISorter.sort(workload.content);
	}

	/**
	 * Sort benchmark with dual pivot qsort implementation.
	 */
	@Benchmark
	@Fork(1)
	@BenchmarkMode(Mode.AverageTime)
	@OutputTimeUnit(TimeUnit.MILLISECONDS)
	@Warmup(iterations = WARMUP_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	@Measurement(iterations = MEASUREMENT_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	public void systemsort(SortingWorkload workload) {
		int[][] cc = workload.content;
		for (int i = 0; i < cc.length; i++) {
			Arrays.sort(cc[i]);
		}
	}

	/**
	 * Sort benchmark with bubble sort implementation.
	 */
	@Benchmark
	@Fork(1)
	@BenchmarkMode(Mode.AverageTime)
	@OutputTimeUnit(TimeUnit.MILLISECONDS)
	@Warmup(iterations = WARMUP_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	@Measurement(iterations = MEASUREMENT_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	public void bubbleSort(SortingWorkload workload) {
		int[][] cc = workload.content;
		for (int i = 0; i < cc.length; i++) {
			bubbleSort(cc[i]);
		}
	}

	/**
	 * Sort benchmark with advanced solution implementation.
	 */
	@Benchmark
	@Fork(1)
	@BenchmarkMode(Mode.AverageTime)
	@OutputTimeUnit(TimeUnit.MILLISECONDS)
	@Warmup(iterations = WARMUP_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	@Measurement(iterations = MEASUREMENT_ITERATIONS, time = 10, timeUnit = TimeUnit.MILLISECONDS)
	public void advancedSort(SortingWorkload workload) {
		// TODO optional task 9b - for mandatory parts, you can leave the code here as
		// it is
		AdvancedJNISorter.sort(workload.content);
	}

	/**
	 * Bubble sort implementation.
	 */
	public static void bubbleSort(int[] c) {
		for (int i = 0; i < c.length - 1; i++) {
			for (int j = 0; j < c.length - i - 1; j++) {
				if (c[j] > c[j + 1]) {
					int tmp = c[j];
					c[j] = c[j + 1];
					c[j + 1] = tmp;
				}
			}
		}
	}

}
