package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.SemaphoreUnorderedGrill;

public class SemaphoreUnorderedGrillTest extends UnorderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new SemaphoreUnorderedGrill(null);
	}
}
