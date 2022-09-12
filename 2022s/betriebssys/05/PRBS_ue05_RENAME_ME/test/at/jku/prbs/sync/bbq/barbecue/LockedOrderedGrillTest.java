package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.LockedOrderedGrill;

public class LockedOrderedGrillTest extends OrderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new LockedOrderedGrill(null);
	}
}
