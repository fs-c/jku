package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.AtomicOrderedGrill;

public class AtomicOrderedGrillTest extends OrderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new AtomicOrderedGrill(null);
	}
}
