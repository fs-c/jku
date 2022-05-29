package at.jku.prbs;


import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import at.jku.prbs.dirmgr.cached.CachedFileHashDMTest;
import at.jku.prbs.dirmgr.cached.PrioritizedCachedFileHashDMTest;
import at.jku.prbs.dirmgr.cached.SpeedCacheTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	CachedFileHashDMTest.class,
	PrioritizedCachedFileHashDMTest.class,
	SpeedCacheTest.class,
})

public class AllTests {}
