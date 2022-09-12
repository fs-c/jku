package at.jku.prbs;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import at.jku.prbs.sync.bbq.barbecue.AtomicOrderedGrillTest;
import at.jku.prbs.sync.bbq.barbecue.LockedOrderedGrillTest;
import at.jku.prbs.sync.bbq.barbecue.LockedUnorderedGrillTest;
import at.jku.prbs.sync.bbq.barbecue.SemaphoreOrderedGrillTest;
import at.jku.prbs.sync.bbq.barbecue.SemaphoreUnorderedGrillTest;
import at.jku.prbs.sync.bbq.barbecue.SynchronizedOrderedGrillTest;
import at.jku.prbs.sync.bbq.party.CountDownLatchPartyTest;
import at.jku.prbs.sync.bbq.party.CyclicBarrierPartyTest;
import at.jku.prbs.sync.bbq.party.PhaserPartyTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	PhaserPartyTest.class,
	CyclicBarrierPartyTest.class,
	CountDownLatchPartyTest.class,
	LockedUnorderedGrillTest.class,
	SemaphoreUnorderedGrillTest.class,
	SynchronizedOrderedGrillTest.class,
	AtomicOrderedGrillTest.class,
	LockedOrderedGrillTest.class,
	SemaphoreOrderedGrillTest.class,
})

public class AllTests {}
