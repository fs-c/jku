package at.jku.prbs.sync.bbq.barbecue;

import org.junit.Before;

import at.jku.prbs.sync.bbq.barbecue.LockedUnorderedGrill;

public class LockedUnorderedGrillTest extends UnorderedGrillTest {

	@Before
	public void setUp() throws Exception {
		grill = new LockedUnorderedGrill(null);
	}
}
