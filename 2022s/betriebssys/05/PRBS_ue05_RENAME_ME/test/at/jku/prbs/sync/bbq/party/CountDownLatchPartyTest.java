package at.jku.prbs.sync.bbq.party;

import org.junit.Before;

import at.jku.prbs.sync.bbq.party.CountDownLatchParty;

public class CountDownLatchPartyTest extends PartyTest {

	@Before
	public void setUp() throws Exception {
		bbqparty = new CountDownLatchParty();
	}
}
