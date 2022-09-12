package at.jku.prbs.sync.bbq.party;

import org.junit.Before;

import at.jku.prbs.sync.bbq.party.CyclicBarrierParty;

public class CyclicBarrierPartyTest extends PartyTest {

	@Before
	public void setUp() throws Exception {
		bbqparty = new CyclicBarrierParty();
	}
}
