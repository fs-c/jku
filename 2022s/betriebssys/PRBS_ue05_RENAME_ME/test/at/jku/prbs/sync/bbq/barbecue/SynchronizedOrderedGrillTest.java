package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.SynchronizedOrderedGrill;

public class SynchronizedOrderedGrillTest extends OrderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new SynchronizedOrderedGrill(null);
	}
}
