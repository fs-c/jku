package at.jku.prbs.dirmgr.cached;

import java.security.NoSuchAlgorithmException;

import net.sf.ehcache.Cache;

/**
 * An extension of the CachedFileHashDM that evicts cache entries based on a custom policy:
 *   - Hashes of files in very volatile paths (var, tmp, etc.) are preferred for eviction.
 *   - Hashes of files with older modification date are preferred for eviction.
 */
public class PrioritizedCachedFileHashDM extends CachedFileHashDM {

	public PrioritizedCachedFileHashDM(String dirPath, int cacheSize) throws NoSuchAlgorithmException {
		super(dirPath, cacheSize);

		Cache hashCache = getCache();
		if (hashCache != null) {
			// set the custom eviction policy
			getCache().setMemoryStoreEvictionPolicy(new PrioritizedMemoryStoreEvictionPolicy(this));
		}
	}
}
