package at.jku.prbs.sync.bbq.barbecue;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class OrderedGrillTest extends BarbecueTest {

	@Test
	public void testOrderedAccess() throws Exception {
		System.out.println("\n--- Ordered access test for " + grill.getClass().getSimpleName() + " ---");
		
		TestParticipant person1 = new TestParticipant(1, grill, null);
		TestParticipant person2 = new TestParticipant(2, grill, null);
		
		person1.start();
		person2.start();
		
		assertFalse(person1.isAtGrill());
		assertFalse(person2.isAtGrill());
		
		grill.setNextActive(person1);
		Thread.sleep(250);
		
		assertTrue(person1.isAtGrill());
		assertFalse(person2.isAtGrill());
		
		person1.continueAndLeave();
		Thread.sleep(250);
		
		assertFalse(person1.isAtGrill());
		assertFalse(person2.isAtGrill());
		
		grill.setNextActive(person2);
		Thread.sleep(250);
		
		assertFalse(person1.isAtGrill());
		assertTrue(person2.isAtGrill());
		
		person2.continueAndLeave();
		Thread.sleep(250);
		
		assertFalse(person1.isAtGrill());
		assertFalse(person2.isAtGrill());
		
		person1.join();
		person2.join();
	}
	
	@Test
	public void testOrderedAccessWithInvitation() throws Exception {
		System.out.println("\n--- Ordered access test with invitation for " + grill.getClass().getSimpleName() + " ---");
		
		TestParticipant invitee = new TestParticipant(1, grill, null);
		TestParticipant inviter = new TestParticipant(2, grill, invitee);	// invites invitee before leaving the grill
		
		invitee.start();
		inviter.start();
		
		assertFalse(invitee.isAtGrill());
		assertFalse(inviter.isAtGrill());
		
		grill.setNextActive(inviter);
		Thread.sleep(250);
		
		assertFalse(invitee.isAtGrill());
		assertTrue(inviter.isAtGrill());
		
		inviter.continueAndLeave();	// invite invitee and leave
		Thread.sleep(250);
		
		assertTrue(invitee.isAtGrill());
		assertFalse(inviter.isAtGrill());
		
		invitee.continueAndLeave();
		Thread.sleep(250);
		
		assertFalse(invitee.isAtGrill());
		assertFalse(inviter.isAtGrill());
		
		invitee.join();
		inviter.join();
	}
}
