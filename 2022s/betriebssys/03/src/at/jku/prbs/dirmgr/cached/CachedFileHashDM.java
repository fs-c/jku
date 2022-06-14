package at.jku.prbs.dirmgr.cached;

import java.io.IOException;
import java.security.NoSuchAlgorithmException;

import net.sf.ehcache.Cache;
import net.sf.ehcache.CacheManager;
import net.sf.ehcache.Element;
import net.sf.ehcache.config.CacheConfiguration;
import net.sf.ehcache.statistics.StatisticsGateway;
import net.sf.ehcache.store.MemoryStoreEvictionPolicy;
import at.jku.prbs.dirmgr.FileHashDM;

/**
 * An extension of the FileHashDM API that caches calculated hashes.
 */
public class CachedFileHashDM extends FileHashDM {

	// default eviction policy for the cache
	private static final MemoryStoreEvictionPolicy HASH_CACHE_EVICTION_POLICY = MemoryStoreEvictionPolicy.LFU;
	
	// name of the cache
	private static final String HASH_CACHE_NAME = "xattr-hash";
	
	// reference to the cache itself
	private final Cache hashCache;
	
	/**
	 * Creates an instance of the pass-through cached FileHashDM with a given cache size.
	 */
	public CachedFileHashDM(String dirPath, int cacheSize) throws NoSuchAlgorithmException {
		super(dirPath);
		
		// ----------------------------------------------------------------------
		// TODO: Configure a new cache instance
		//       Hint: You will certainly need to modify the line "hashCache = null".
		//       Hint: The name for the cache is in the constant HASH_CACHE_NAME.
		//       Hint: The cache should hold up to cacheSize elements.
		//       Hint: The eviction policy for the cache is in the constant
		//             HASH_CACHE_EVICTION_POLICY.
		// ----------------------------------------------------------------------
		var configuration = new CacheConfiguration()
				.name(HASH_CACHE_NAME)
				.memoryStoreEvictionPolicy(HASH_CACHE_EVICTION_POLICY)
				.maxEntriesLocalHeap(cacheSize);
		
		hashCache = new Cache(configuration);
		// ----------------------------------------------------------------------
		
		// ----------------------------------------------------------------------
		// TODO: Add the cache instance to the cache manager
		//       Hint: Use CacheManager.getInstance() to get/create the CacheManager.
		// ----------------------------------------------------------------------
		// ----------------------------------------------------------------------
		
		var manager = CacheManager.getInstance();
		manager.addCache(hashCache);
	}
	
	/**
	 * Get the cache instance.
	 * 
	 * @return The cache instance
	 */
	protected Cache getCache() {
		return hashCache;
	}
	
	/**
	 * Performs cleanup of the directory manager API and prints cache statistics.
	 */
	public void cleanupAndPrintStatistics() {
		final StatisticsGateway statistics = hashCache.getStatistics();
		
		long hits = statistics.cacheHitCount();
		long misses = statistics.cacheMissCount();
		double hitRatio = Math.round(((double) hits) / (hits + misses) * 100);
		
		System.out.println("Cache statistics:");
		
		System.out.println("  - puts:        " + statistics.cachePutCount());
		System.out.println("    - added:     " + statistics.cachePutAddedCount());
		System.out.println("    - updated:   " + statistics.cachePutUpdatedCount());
		
		System.out.println("  - expirations: " + statistics.cacheExpiredCount());
		System.out.println("  - evictions:   " + statistics.cacheEvictedCount());
		System.out.println("  - removals:    " + statistics.cacheRemoveCount());
		
		System.out.println("  - hits:        " + hits);
		System.out.println("  - misses:      " + misses);
		System.out.println("    - not found: " + statistics.cacheMissNotFoundCount());
		System.out.println("    - expired:   " + statistics.cacheMissExpiredCount());
		System.out.println("  - hit ratio:   " + hitRatio + "%");
		
		// shut down the cache manager
		CacheManager.getInstance().shutdown();
	}
	
	/**
	 * Computes the hash over the data of a given file.
	 * 
	 * @param subPath Path to the file for which a hash should be computed
	 * @return Computed hash value as byte array
	 * @throws IOException
	 */
	@Override
	protected byte[] computeHash(final String subPath) throws IOException {
		// ----------------------------------------------------------------------
		// TODO: Implement caching
		//       Hint: Check if there is an existing entry for the path in the cache.
		//             Use that entry on cache hit or use the super-class to perform
		//             the actual computation on cache miss. Don't forget to add the
		//             newly computed element to the cache.
		// ----------------------------------------------------------------------
		var cachedElement = hashCache.get(subPath);
		if (cachedElement != null) {
			return (byte[]) cachedElement.getObjectValue();
		}
		
		var hash = super.computeHash(subPath);
		
		hashCache.put(new Element(subPath, hash));
		
		return hash;
		// ----------------------------------------------------------------------
	}

	/**
	 * Renames the given file (path) and updates that file's hash entry in the cache,
	 * if the rename operation succeeded.
	 * 
	 * @param subPathOld Current path to the file that should be renamed
	 * @param subPathNew New path for the file
	 * @throws IOException 
	 */
	@Override
	public void renameFile(String subPathOld, String subPathNew) throws IOException {
		super.renameFile(subPathOld, subPathNew);
		
		// ----------------------------------------------------------------------
		// TODO: Modify the cache entry
		//       Hint: You may remove the current entry and add a new one, if necessary.
		//       Hint: super.renameFile() throws an exception on failure, so you
		//             may safely assume successful rename from this point on.
		// ----------------------------------------------------------------------
		// ----------------------------------------------------------------------
		
		var entry = hashCache.removeAndReturnElement(subPathOld);
		hashCache.put(new Element(subPathNew,
			entry != null ? entry.getObjectValue() : super.computeHash(subPathNew)));
	}

	/**
	 * Unlinks the given file (path) and removes that file's hash from the cache,
	 * if the unlink operation succeeded.
	 * 
	 * @param subPath Path to the file that should be deleted
	 * @throws IOException 
	 */
	@Override
	public void deleteFile(String subPath) throws IOException {
		super.deleteFile(subPath);

		// ----------------------------------------------------------------------
		// TODO: Modify the cache entry
		//       Hint: super.deleteFile() throws an exception on failure, so you
		//             may safely assume successful removal from this point on.
		// ----------------------------------------------------------------------
		// ----------------------------------------------------------------------
		
		hashCache.remove(subPath);
	}
}
