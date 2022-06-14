package at.jku.prbs.dirmgr.cached;

import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import net.sf.ehcache.Element;
import net.sf.ehcache.store.Policy;
import at.jku.prbs.dirmgr.FileHashDM;

/**
 * Custom eviction policy that evicts entries of more volatile origin, or older modification time.
 */
public class PrioritizedMemoryStoreEvictionPolicy implements Policy {

	private static final int FIRST = 0;
	private static final int SECOND = 1;
	
	private FileHashDM directoryManager;
	
	/**
	 * Create policy and store reference to underlying directory manager API
	 * (we'll need it later to query the modification time).
	 */
	public PrioritizedMemoryStoreEvictionPolicy(PrioritizedCachedFileHashDM directoryManager) {
		this.directoryManager = directoryManager;
	}
	
	@Override
	public String getName() {
		return "PRIORITIZED";
	}

	/**
	 * Selects an element to evict from a set of sample elements. Also gets a reference
	 * to the just added element, because we don't want to remove that one.
	 * 
	 * @param sampledElements This is a random subset of the population.
     * @param justAdded We probably never want to select the element just added. It is provided so that it can be ignored if selected. May be null.
	 */
	@Override
	public Element selectedBasedOnPolicy(Element[] sampledElements, Element justAdded) {
		if (sampledElements.length > 1) {
			// sort the elements by their path volatility score
			ScoredElement[] scoredElements = new ScoredElement[sampledElements.length];
			for (int i = 0; i < sampledElements.length; ++i) {
				Element element = sampledElements[i];
				scoredElements[i] = new ScoredElement(element, calculatePathScore(element));
			}
			Arrays.sort(scoredElements, new ScoredElementComparator());
			
			// ----------------------------------------------------------------------
			// TODO: Find out which element should be removed from the cache and return that element.
			//       Hint: Determine the first two elements in the sorted list. Retain the
			//             first candidate if it has just been added, and evict the second one.
			//             Evict the first candidate if the second one has just been added.
			//             Evict the first candidate if it has a smaller volatility score than
			//             the second one (keep in mind that the list is already sorted based
			//             on that score). In case of a score tie between first and second,
			//             decide based on the modification time and the hit counter (note that
			//             compareByModificationTime() does exactly that.)
			// ----------------------------------------------------------------------
			// ----------------------------------------------------------------------
			
			var first = scoredElements[0];
			var second = scoredElements[1];
			
			if (first.getElement() == justAdded) {
				return second.getElement();
			} else if (second.getElement() == justAdded) {
				return first.getElement();
			}
			
			if (first.getScore() == second.getScore()) {
				if (compareByModificationTime(first.getElement(), second.getElement())) {
					return second.getElement();
				} else {
					return first.getElement();
				}
			} else {
				return first.getElement();
			}
		}
		
		// with just a single element, there is not much choice
		return sampledElements[FIRST];
	}

	/**
	 * Compares two elements and determines which one to evict:
	 *  - true: second element
	 *  - false: first element
	 * Compares by their path volatility score.
	 */
	@Override
	public boolean compare(Element element1, Element element2) {
		return compareByPathScore(element1, element2);
	}
	
	/**
	 * Compares two elements and determines which one to evict:
	 *  - true: second element
	 *  - false: first element
	 * Compares by their path volatility score, and, in case of equal scores,
	 * continues by comparing based on the modification time.
	 */
	private boolean compareByPathScore(Element element1, Element element2) {
		// ----------------------------------------------------------------------
		// TODO: Find out which of the two elements should be removed from the cache.
		//       Hint: Determine the volatility score with calculatePathScore().
		//       Hint: Evict the first candidate if it has a smaller volatility score than
		//             the second one or evict the second one if the first one has a higher
		//             volatility score. In case of a score tie between first and second,
		//             use compareByModificationTime() to decide.
		// ----------------------------------------------------------------------
		
		var score1 = calculatePathScore(element1);
		var score2 = calculatePathScore(element2);
		
		return score1 == score2 ? compareByModificationTime(element1, element2) : score1 < score2;
		// ----------------------------------------------------------------------
	}
	
	/**
	 * Calculates the volatility score for the path of a given element.
	 */
	private int calculatePathScore(Element element) {
		String path = (String)element.getObjectKey();
		return PathVolatilityLevel.getScore(path);
	}
	
	/**
	 * Compares two elements and determines which one to evict:
	 *  - true: second element (is older)
	 *  - false: first element (is older)
	 * Compares by their modification time, and, in case of equal times,
	 * selects element2 if its hit count is smaller.
	 * @throws IOException 
	 */
	private boolean compareByModificationTime(Element element1, Element element2) {
		// ----------------------------------------------------------------------
		// TODO: Find out which of the two elements should be removed from the cache.
		//       Hint: Determine the modification time with getModificationTime().
		//       Hint: Evict the first candidate if it is older than the second one or
		//             evict the second one if the first one is newer. In case of a
		//             tie between first and second, compare the hit count of the
		//             two cache elements and use the one that was hit less frequently.
		// ----------------------------------------------------------------------
		
		var time1 = getModificationTime(element1);
		var time2 = getModificationTime(element2);
		
		return time1 == time2 ? element1.getHitCount() > element2.getHitCount() : time1 > time2;
		// ----------------------------------------------------------------------
	}
	
	/**
	 * Queries the modification for the file (path) referenced by the given element.
	 * @throws IOException 
	 */
	private long getModificationTime(Element element) {
		String path = (String)element.getObjectKey();
		
		long mTime;
		try {
			mTime = directoryManager.getFileAttributes(path).lastModifiedTime().toMillis();
		} catch (IOException e) {
			// Error: set modification time to 0 --> very old file
			mTime = 0;
		}
		
		return mTime;
	}
	
	/**
	 * Encapsulates an element and its (volatility) score.
	 */
	private static class ScoredElement {
		
		private Element element;
		private int score;
		
		public ScoredElement(Element element, int score) {
			this.element = element;
			this.score = score;
		}
		
		public Element getElement() {
			return element;
		}

		public int getScore() {
			return score;
		}

		@Override
		public String toString() {
			return element.getObjectKey() + " - score: " + score;
		}
	}
	
	/**
	 * Compares to ScoredElement objects by their score.
	 */
	private static class ScoredElementComparator implements Comparator<ScoredElement> {

		@Override
		public int compare(ScoredElement e1, ScoredElement e2) {
			return e1.getScore() - e2.getScore();
		}
		
	}
	
	/**
	 * The different volatility levels and a method to get the score for a given path.
	 */
	private static enum PathVolatilityLevel {
		VERY_VOLATILE(-20, Arrays.asList("proc", "tmp", "var")),
		VOLATILE(-10, Arrays.asList("media", "mnt", "run", "sys")),
		NORMAL(0, Arrays.asList("home", "root")),
		STABLE(10, Arrays.asList("cdrom", "dev", "etc", "lost+found", "srv")),
		VERY_STABLE(20, Arrays.asList("boot", "bin", "lib", "lib32", "lib64", "libx32", "opt", "sbin", "usr"));
		
		private int score;
		private List<String> paths;
		
		private PathVolatilityLevel(int score, List<String> paths) {
			this.score = score;
			this.paths = paths;
		}
		
		public static int getScore(String path) {
			for (PathVolatilityLevel volatilityLevel : PathVolatilityLevel.values()) {
				for (String levelPath : volatilityLevel.paths) {
					if (path.startsWith(levelPath)) {
						return volatilityLevel.score;
					}
				}
			}
			return NORMAL.score;
		}
	}
}
