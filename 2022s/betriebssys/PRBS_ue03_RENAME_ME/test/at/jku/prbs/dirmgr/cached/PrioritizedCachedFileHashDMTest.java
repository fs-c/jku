package at.jku.prbs.dirmgr.cached;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;

import net.sf.ehcache.statistics.StatisticsGateway;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import at.jku.prbs.dirmgr.DirectoryManagerTest;

public class PrioritizedCachedFileHashDMTest extends DirectoryManagerTest {

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
		} catch(InvalidPathException e){
			fail("Path to the test file system tree not set. Set the constant DirectoryManagerTest.TEST_FS_PATH to the correct directory!");
		}
	}

	@After
	public void tearDown() throws Exception {
		if (testDirectoryManager != null) {
			testDirectoryManager.cleanupAndPrintStatistics();
		}
	}
	
	@Test
	public void testOneSlot() throws Exception {
		System.out.println("\n--- Testing cache with 1 slot ---");
		
		testDirectoryManager = new PrioritizedCachedFileHashDM(rootPath.toString(), 1);
		
		String hostFilePath = Paths.get("etc", "hosts").toString();
		
		// miss and put
		testDirectoryManager.getFileHash(hostFilePath);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cachePutCount());
		assertEquals(1, statistics.cacheMissCount());
		
		// hit
		testDirectoryManager.getFileHash(hostFilePath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheHitCount());
		
		// another hit
		testDirectoryManager.getFileHash(hostFilePath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cacheHitCount());
		
		// miss, eviction, and put
		testDirectoryManager.getFileHash(Paths.get("etc", "protocols").toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cacheMissCount());
		assertEquals(1, statistics.cacheEvictedCount());
		assertEquals(2, statistics.cachePutCount());
	}

	@Test
	public void testNoEvictionOfFirstJustAdded() throws Exception {
		System.out.println("\n--- Testing cache where the most likely to be evicted candidate "
								+ "is retained because it was just added ---");
		
		testDirectoryManager = new PrioritizedCachedFileHashDM(rootPath.toString(), 2);
		
		String lowVolatilityPath = Paths.get("etc", "hosts").toString();
		String normalVolatilityPath = Paths.get("home", "ins", ".bashrc").toString();
		String highVolatilityPath = Paths.get("var", "log", "messages").toString();
		
		// fill cache with elements of lower volatility
		testDirectoryManager.getFileHash(lowVolatilityPath);
		testDirectoryManager.getFileHash(normalVolatilityPath);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cachePutCount());
		assertEquals(2, statistics.cacheMissCount());
		
		// just added high volatility element would be evicted, but isn't
		testDirectoryManager.getFileHash(highVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cachePutCount());
		assertEquals(3, statistics.cacheMissCount());
		assertEquals(1, statistics.cacheEvictedCount());
		
		// as can be seen by the hit when querying its hash again
		testDirectoryManager.getFileHash(highVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(1, statistics.cacheHitCount());
	}
	
	@Test
	public void testNoEvictionOfSecondJustAdded() throws Exception {
		System.out.println("\n--- Testing cache where the second candidate is "
							+ "retained because it was just added ---");
		testDirectoryManager = new PrioritizedCachedFileHashDM(rootPath.toString(), 2);
		
		String lowVolatilityPath = Paths.get("etc", "hosts").toString();
		String normalVolatilityPath = Paths.get("home", "ins", ".bashrc").toString();
		String highVolatilityPath = Paths.get("var", "log", "messages").toString();
		
		// fill cache with elements of mixed volatility
		testDirectoryManager.getFileHash(lowVolatilityPath);
		testDirectoryManager.getFileHash(highVolatilityPath);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cachePutCount());
		assertEquals(2, statistics.cacheMissCount());
		
		// just added element as 2nd candidate lets 1st candidate being evicted immediately
		testDirectoryManager.getFileHash(normalVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cachePutCount());
		assertEquals(3, statistics.cacheMissCount());
		assertEquals(1, statistics.cacheEvictedCount());
		
		// as can be seen by the miss when querying the element with high volatility again
		testDirectoryManager.getFileHash(highVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(4, statistics.cacheMissCount());
	}
	
	@Test
	public void testEvictionBasedOnVolatility() throws Exception {
		System.out.println("\n--- Testing cache where the first entry is evicted because of its score ---");
		
		testDirectoryManager = new PrioritizedCachedFileHashDM(rootPath.toString(), 2);
		
		String lowVolatilityPath = Paths.get("etc", "hosts").toString();
		String normalVolatilityPath = Paths.get("home", "ins", ".bashrc").toString();
		String highVolatilityPath = Paths.get("var", "log", "messages").toString();
		
		// fill cache with elements in decreasing volatility
		testDirectoryManager.getFileHash(highVolatilityPath);
		testDirectoryManager.getFileHash(normalVolatilityPath);
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cachePutCount());
		assertEquals(2, statistics.cacheMissCount());
		
		// when adding element with low volatility, candidate with highest volatility is evicted
		testDirectoryManager.getFileHash(lowVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cachePutCount());
		assertEquals(3, statistics.cacheMissCount());
		assertEquals(1, statistics.cacheEvictedCount());
		
		// as can be seen by the miss when querying the element with high volatility again
		testDirectoryManager.getFileHash(highVolatilityPath);
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(4, statistics.cacheMissCount());
	}
	
	@Test
	public void testEvictionBasedOnMTime() throws Exception {
		System.out.println("\n--- Testing cache where the entry is evicted because of its age ---");
		
		testDirectoryManager = new PrioritizedCachedFileHashDM(rootPath.toString(), 2);
		
		Path olderFilePath = Paths.get("tmp", "older");
		Path newerFilePath = Paths.get("tmp", "newer");
		Path lowVolatilityPath = Paths.get("etc", "hosts");
		
		Path olderRealFilePath = rootPath.resolve(olderFilePath).normalize().toAbsolutePath();
		Path newerRealFilePath = rootPath.resolve(newerFilePath).normalize().toAbsolutePath();
		Files.deleteIfExists(olderRealFilePath);
		Files.deleteIfExists(newerRealFilePath);
		
		Files.createFile(olderRealFilePath);
		Thread.sleep(1500);
		Files.createFile(newerRealFilePath);
		
		// fill cache with hashes of just created files with high volatility
		testDirectoryManager.getFileHash(olderFilePath.toString());
		testDirectoryManager.getFileHash(newerFilePath.toString());
		StatisticsGateway statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(2, statistics.cachePutCount());
		assertEquals(2, statistics.cacheMissCount());
		
		// when adding element with low volatility, tie between the two high volatility
		// files is broken by evicting the older one
		testDirectoryManager.getFileHash(lowVolatilityPath.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(3, statistics.cachePutCount());
		assertEquals(3, statistics.cacheMissCount());
		assertEquals(1, statistics.cacheEvictedCount());
		
		// as can be seen by the miss when querying the hash of the older file
		testDirectoryManager.getFileHash(olderFilePath.toString());
		statistics = testDirectoryManager.getCache().getStatistics();
		assertEquals(4, statistics.cacheMissCount());
		
		Files.deleteIfExists(olderRealFilePath);
		Files.deleteIfExists(newerRealFilePath);
	}
	
}
