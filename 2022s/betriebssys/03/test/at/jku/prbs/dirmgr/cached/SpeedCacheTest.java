package at.jku.prbs.dirmgr.cached;

import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Random;

import org.junit.Before;
import org.junit.Test;

import at.jku.prbs.dirmgr.DirectoryManagerTest;
import at.jku.prbs.dirmgr.FileHashDM;
import at.jku.prbs.dirmgr.visitors.ReadAllRegularFilesVisitor;

public class SpeedCacheTest extends DirectoryManagerTest {

	private Path rootPath = null;
	
	@Before
	public void setUp() throws Exception {
		try {
			assertNotEquals("Path to the test file system tree not set. Set the constant DirectoryManagerTest.TEST_FS_PATH to the correct directory!",
					"<PATH TO TEST FILE SYSTEM>", TEST_FS_PATH);
			
			Path p = Paths.get(TEST_FS_PATH);
			assertTrue("Path of the test file system tree does not exist! Set the constant DirectoryManagerTest.TEST_FS_PATH to a valid directory!",
					Files.exists(p) && Files.isDirectory(p));
			
			rootPath = Paths.get(TEST_FS_PATH).toAbsolutePath().normalize();
		} catch(InvalidPathException e){
			fail("Path to the test file system tree not set. Set the constant DirectoryManagerTest.TEST_FS_PATH to the correct directory!");
		}
	}

	@Test
	public void testSingleSubdirSpeedTest() throws Exception {
		System.out.println("\n--- Testing single subdir file system ---");
		
		int cacheSize = 300;
		
		ReadAllRegularFilesVisitor findFileVisitor = 
				new ReadAllRegularFilesVisitor(rootPath);
		Files.walkFileTree(rootPath.resolve("etc"), findFileVisitor);
		
		RandomHashTester tester = new RandomHashTester(500, findFileVisitor.getResults());

		testAllFS(cacheSize, tester);
	}

	@Test
	public void testOvercommitPersistentDirSpeedTest() throws Exception {
		System.out.println("\n--- Testing overcommited persistent file system ---");
		
		int cacheSize = 3000;
		
		ReadAllRegularFilesVisitor findFileVisitor = 
				new ReadAllRegularFilesVisitor(rootPath);
		Files.walkFileTree(rootPath.resolve("etc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("etc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("etc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("etc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("bin"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("bin"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("bin"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("proc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("proc"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("tmp"), findFileVisitor);
		Files.walkFileTree(rootPath.resolve("tmp"), findFileVisitor);
		
		RandomHashTester tester = new RandomHashTester(6000, findFileVisitor.getResults());

		testAllFS(cacheSize, tester);
	}
	
	@Test
	public void testWholeFSCacheSpeedTest() throws Exception {
		System.out.println("\n--- Testing whole file system ---");
		
		int cacheSize = 1000;

		ReadAllRegularFilesVisitor findFileVisitor = 
				new ReadAllRegularFilesVisitor(rootPath);
		Files.walkFileTree(rootPath, findFileVisitor);
		
		RandomHashTester tester = new RandomHashTester(3000, findFileVisitor.getResults());

		testAllFS(cacheSize, tester);
	}



	private void testAllFS(int cacheSize, RandomHashTester tester) throws Exception {
		System.out.println("\n--- Testing HashFS ---");
		
		FileHashDM testHashFS = new FileHashDM(rootPath.toString());
		
		long start = System.nanoTime();
		tester.test(testHashFS);
		long hashFStime = (System.nanoTime() - start) / 1000000L;

		
		System.out.println("\n--- Testing CachedFS ---");
		
		CachedFileHashDM testCachedFS = new CachedFileHashDM(rootPath.toString(), cacheSize);
		start = System.nanoTime();
		tester.test(testCachedFS);
		long cachedFStime = (System.nanoTime() - start) / 1000000L;
		testCachedFS.cleanupAndPrintStatistics();

		System.out.println("\n--- Testing PrioritizedCacheFS ---");
		PrioritizedCachedFileHashDM testPrioritizedFS = new PrioritizedCachedFileHashDM(rootPath.toString(), cacheSize);
		start = System.nanoTime();
		tester.test(testPrioritizedFS);
		long prioritizedFStime = (System.nanoTime() - start) / 1000000L;
		testPrioritizedFS.cleanupAndPrintStatistics();

		System.out.format("FileHashDM execution time: %,d ms\n", hashFStime);
		System.out.format("CachedFileHashDM execution time: %,d ms\n", cachedFStime);
		System.out.format("PrioritizedCachedFileHashDM execution time: %,d ms\n", prioritizedFStime);
	}


	private class RandomHashTester {
		protected int randomLookups;
		String[] randomLookupPaths;
		
		RandomHashTester(int randomLookups, String[] randomLookupPaths) {
			this.randomLookups = randomLookups;
			this.randomLookupPaths = randomLookupPaths;
		}
		
		public void test(FileHashDM hashDM) throws Exception {
			Random r = new Random();
			for (int i = 0; i < randomLookups; ++i) {
				hashDM.getFileHash(randomLookupPaths[r.nextInt(randomLookupPaths.length)]);
			}
		}
	}
}
