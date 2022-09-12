package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.SemaphoreOrderedGrill;

public class SemaphoreOrderedGrillTest extends OrderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new SemaphoreOrderedGrill(null);
	}
}
