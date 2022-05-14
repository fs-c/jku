package at.jku.prbs.dirmgr.cached;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;

import net.sf.ehcache.statistics.StatisticsGateway;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import at.jku.prbs.dirmgr.DirectoryManagerTest;
import at.jku.prbs.dirmgr.visitors.FindHashAttributeFileVisitor;
import at.mroland.utils.StringUtils;

public class CachedFileHashDMTest extends DirectoryManagerTest {

	private static final Path TEST_FILE_PATH = Paths.get("tmp", "hashCacheTestFile");
	
	private CachedFileHashDM testDirectoryManager = null;
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
			
			deleteFile(TEST_FILE_PATH);
		} catch(InvalidPathException e){
			fail("Path to the test file system tree not set. Set the constant DirectoryManagerTest.TEST_FS_PATH to the correct directory!");
		}
	}

	@After
	public void tearDown() throws Exception {
		if (testDirectoryManager != null) {
			testDirectoryManager.cleanupAndPrintStatistics();
		}
		
		deleteFile(TEST_FILE_PATH);
	}
	
	private void deleteFile(Path filePath) throws IOException {
		Path realTestFilePath = rootPath.resolve(filePath).normalize().toAbsolutePath();
		Files.deleteIfExists(realTestFilePath);
	}
	
	@Test
	public void testSingleReadHashAttribute() throws Exception {
		System.out.println("\n--- Testing single read of hash attribute ---");
		
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), 3);
		createFileAndCheckHash(1, true);
		
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cachePutCount());
		assertEquals(0, statistics.cacheHitCount());
		assertEquals(statistics.cacheMissCount(), statistics.cachePutCount());
	}
	
	@Test
	public void testMultipleReadHashAttribute() throws Exception {
		System.out.println("\n--- Testing multiple reads of hash attribute ---");
		
		// 100 reads should show the (positive) effects of the cache
		int iterations = 100;
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), 1);
		createFileAndCheckHash(iterations, true);
		
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cachePutCount());
		assertEquals(statistics.cacheHitCount(), iterations - 1);
		assertEquals(statistics.cacheMissCount(), statistics.cachePutCount());
	}

	@Test
	public void testSingleSearchForHashInFS() throws Exception {
		System.out.println("\n--- Testing single search for file with specific hash ---");
		
		int cacheSize = 850;
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), cacheSize);
		createFileAndSearchHash(1);
		
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertTrue(statistics.cachePutCount() > cacheSize);
		assertEquals(statistics.cacheHitCount(), 0);
		assertEquals(statistics.cacheMissCount(), statistics.cachePutCount());
		assertTrue(statistics.cacheEvictedCount() > 0);
	}
	
	@Test
	public void testMultipleSearchForHashInFS() throws Exception {
		System.out.println("\n--- Testing multiple searches for file with specific hash ---");
		
		// Two searches should already show the benefits of a cache
		int cacheSize = 850;
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), cacheSize);
		createFileAndSearchHash(2);
		
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		long hits = statistics.cacheHitCount();
		long misses = statistics.cacheMissCount();
		double hitRatio = Math.round(((double) hits) / (hits + misses) * 100);

		// Hit ratio should be a bit below 50 per cent (first round -> no hits, second --> almost all)
		assertTrue(35 < hitRatio && hitRatio < 50);
		assertTrue(statistics.cacheEvictedCount() > 0);
	}

	
	@Test
	public void testMoveOnSuccessfulRename() throws Exception {
		System.out.println("\n--- Testing deletion of hash entry when renaming the file ---");
		
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), 3);
		deleteFile(Paths.get(TEST_FILE_PATH.toString() + ".new"));
		
		// create file and query its hash => gets cached
		createFileAndCheckHash(1, false);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(0, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
		
		// query hash again => generates cache hit
		testDirectoryManager.getFileHash(TEST_FILE_PATH.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
		
		// rename file => finds old name in cache, removes cache entry, adds new entry
		testDirectoryManager.renameFile(TEST_FILE_PATH.toString(), TEST_FILE_PATH.toString() + ".new");
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheRemoveCount());
		assertEquals(2, statistics.cachePutCount());
		assertEquals(2, statistics.cacheHitCount());  // note: one extra hit due to logging with hash
		
		// query new hash => generates cache hit
		testDirectoryManager.getFileHash(TEST_FILE_PATH.toString() + ".new");
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
		
		deleteFile(Paths.get(TEST_FILE_PATH.toString() + ".new"));
	}
	
	@Test
	public void testNoRemovalOnUnsuccessfulRename() throws Exception {
		System.out.println("\n--- Testing retaining of hash entry when renaming the file has failed ---");
		
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), 3);
		
		// create file and query its hash => gets cached, let rename fail => no removal
		createFileAndCheckHash(1, false);
		testDirectoryManager.getFileHash(TEST_FILE_PATH.toString());
		try {
			// Provoke exception
			testDirectoryManager.renameFile(TEST_FILE_PATH.toString(), "tmp");
		} catch (IOException e) {
			// Ignore the intentionally provoked exception (try if file was not removed from cache)
		}
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(0, statistics.cacheRemoveCount());
		assertEquals(1, statistics.cachePutCount());
		assertEquals(2, statistics.cacheHitCount());  // note: one extra hit due to logging with hash
		
		// query (still-cashed) hash again => generates cache hit
		testDirectoryManager.getFileHash(TEST_FILE_PATH.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
	}
	
	@Test
	public void testRemoveOnSuccessfulDelete() throws Exception {
		System.out.println("\n--- Testing deletion of hash entry when unlinking the file ---");
		testDirectoryManager = new CachedFileHashDM(rootPath.toString(), 3);
		
		// create file and query its hash => gets cached
		createFileAndCheckHash(1, false);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(0, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
		
		// query hash again => generates cache hit
		testDirectoryManager.getFileHash(TEST_FILE_PATH.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheHitCount());
		assertEquals(1, statistics.cacheMissCount());
		
		// unlink file => removes cache entry
		testDirectoryManager.deleteFile(TEST_FILE_PATH.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheRemoveCount());
		
		// query hash again => generates cache miss
		createFileAndCheckHash(1, false);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cacheHitCount());  // note: one extra hit due to logging with hash
		assertEquals(2, statistics.cacheMissCount());
	}
	
	private void createFileAndCheckHash(int nrChecks, boolean deleteAfterwards) throws Exception {
		createFileAndTest(TEST_FILE_PATH, new ConfigurableIterationHashTest(nrChecks) {
			
			@Override
			protected void testSingle(String filePath, String expectedHash) throws IOException {
				byte[] queriedHash = testDirectoryManager.getFileHash(filePath);
				assertArrayEquals("hash not stored/computed correctly",
						StringUtils.hexToBytes(expectedHash), queriedHash);
			}
		}, deleteAfterwards);
	}

	private void createFileAndSearchHash(int nrSearches) throws Exception {
		createFileAndTest(TEST_FILE_PATH, new ConfigurableIterationHashTest(nrSearches) {
			
			@Override
			protected void testSingle(String filePath, String expectedHash) throws Exception {
				FindHashAttributeFileVisitor findFileVisitor = 
						new FindHashAttributeFileVisitor(expectedHash, rootPath, testDirectoryManager);
				Files.walkFileTree(rootPath, findFileVisitor);
				
				Path expectedPath = Paths.get("/").resolve(filePath);
				boolean foundFile = false;
				for (String matchingFile : findFileVisitor.getResults()) {
					if (Paths.get(matchingFile).equals(expectedPath)){
						foundFile = true;
					}
				}
				assertTrue("Did not find the created file. Generated hash does not match?", foundFile);
			}
		}, true);
	}

	private void createFileAndTest(Path filePath, ConfigurableIterationHashTest tester,
									boolean deleteAfterwards) throws Exception {
		String expectedHash = "ce41e5246ead8bddd2a2b5bbb863db250f328be9dc5c3041481d778a32f8130d";
		Path realFilePath = rootPath.resolve(filePath).normalize().toAbsolutePath();
		
		try {
			// create the file and insert known data (hash conforms with this data)
			Files.createFile(realFilePath);
			Files.write(realFilePath, new byte[] {'t','e','s','t','d','a','t','a','\n'});

			// run tester
			tester.test(filePath.toString(), expectedHash);
			
		} catch (IOException e) {
			e.printStackTrace();
			fail("IO Exception in excecution: " + e.toString());
		} finally {
			try {
				if (deleteAfterwards) {
					deleteFile(filePath);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	private abstract class ConfigurableIterationHashTest {
		protected int iterations;
		
		ConfigurableIterationHashTest(int iterations) {
			this.iterations = iterations;
		}
		
		public void test(String filePath, String expectedHash) throws Exception {
			for (int i = 0; i < iterations; ++i) {
				testSingle(filePath, expectedHash);
			}
		}
		
		protected abstract void testSingle(String filePath, String expectedHash) throws Exception;
	}
}
