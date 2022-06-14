package at.jku.prbs.sync.bbq.barbecue;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class UnorderedGrillTest extends BarbecueTest {
	
	private static final int NR_ROUNDS = 5;

	@Test
	public void testUnorderedAccess() throws Exception {
		for (int i = 0; i < NR_ROUNDS; i++) {
			System.out.println("\n--- Unordered access test for " + grill.getClass().getSimpleName() + " #" + i + " ---");
			
			TestParticipant person1 = new TestParticipant(1, grill, null);
			TestParticipant person2 = new TestParticipant(2, grill, null);
			
			assertFalse(person1.isAtGrill());
			assertFalse(person2.isAtGrill());
			
			person1.start();
			person2.start();
			
			assertAndContinue(person1, person2);
			assertAndContinue(person1, person2);
			
			person1.join();
			person2.join();
		}
	}
	
	protected void assertAndContinue(TestParticipant person1, TestParticipant person2) throws Exception {
		Thread.sleep(250);
		assertTrue(person1.isAtGrill() != person2.isAtGrill());
		
		if (person1.isAtGrill()) {
			person1.continueAndLeave();
		} else {
			person2.continueAndLeave();
		}
	}
}
