package at.jku.prbs.sync.bbq.party;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import at.jku.prbs.sync.bbq.party.AbstractParty;
import at.jku.prbs.sync.bbq.party.BBQParty;
import at.jku.prbs.sync.bbq.party.BBQParty.Phase;

public class PartyTest {

	protected BBQParty bbqparty;
	private final ExecutorService participantPool = Executors.newFixedThreadPool(AbstractParty.MAX_GUESTS_TO_PREP * 2);
	
	@Rule
	public ExpectedException exception = ExpectedException.none();
	
	@Test
	public void testFirstPhaseRunningInTheBeginning() throws Exception {
		assertEquals(Phase.get(0), bbqparty.getRunningPhase());
	}

	@Test
	public void testNoPhasesCompletedInTheBeginning() throws Exception {
		assertTrue(bbqparty.getCompletedPhases().isEmpty());
	}
	
	@Test
	public void testCannotMissPhase() throws Exception {
		exception.expect(IllegalArgumentException.class);
		bbqparty.waitForEndOf(Phase.PAYING_AND_LEAVING);
	}
	
	@Test
	public void testSingularCompletionAndWaiting() throws Exception {
		List<Future<?>> participants = new ArrayList<Future<?>>();
		Phase[] firstPhase = new Phase[] { Phase.ENTERING_AND_SEATING };
		
		for (int i = 0; i < AbstractParty.MAX_GUESTS_TO_PREP; i++) {
			participants.add(letParticipantCompleteAndWaitForEndOf(firstPhase));
		}
		
		for (Future<?> p: participants) {
			assertFalse(p.isDone());
		}
		
		participants.add(letParticipantCompleteAndWaitForEndOf(firstPhase));
		
		for (Future<?> p: participants) {
			p.get();
			assertTrue(p.isDone());
		}
		
		assertEquals(1, bbqparty.getCompletedPhases().size());
		assertTrue(bbqparty.getCompletedPhases().contains(Phase.ENTERING_AND_SEATING));
	}
	
	@Test
	public void testMultipleCompletionAndWaiting() throws Exception {
		List<Future<?>> participantsWaitingForEndOfSecondPhase = new ArrayList<Future<?>>();
		Phase[] firstPhase = new Phase[] { Phase.ENTERING_AND_SEATING };
		Phase[] secondPhase = new Phase[] { Phase.ORDERING_AND_EATING };
		Phase[] firstAndSecondPhase = new Phase[] { Phase.ENTERING_AND_SEATING, Phase.ORDERING_AND_EATING};
		
		for (int i = 0; i < AbstractParty.MAX_SEATS; i++) {
			participantsWaitingForEndOfSecondPhase.add(letParticipantCompleteAndWaitForEndOf(firstAndSecondPhase));
		}
		
		for (Future<?> p: participantsWaitingForEndOfSecondPhase) {
			assertFalse(p.isDone());
		}
		
		List<Future<?>> participantEndingAfterFirstPhase = new ArrayList<Future<?>>(); 
		for (int i = 0; i < (AbstractParty.MAX_GUESTS_TO_PREP - AbstractParty.MAX_SEATS + 1); i++) {
			participantEndingAfterFirstPhase.add(letParticipantCompleteAndWaitForEndOf(firstPhase));
		}
		Thread.sleep(250);
		
		for (Future<?> p:  participantEndingAfterFirstPhase) {
			assertTrue(p.isDone());
		}
		for (Future<?> p: participantsWaitingForEndOfSecondPhase) {
			assertFalse(p.isDone());
		}
		
		Future<?> participantEndingAfterSecondPhase = letParticipantCompleteAndWaitForEndOf(secondPhase);
		Thread.sleep(250);
		
		assertTrue(participantEndingAfterSecondPhase.isDone());
		for (Future<?> p: participantsWaitingForEndOfSecondPhase) {
			assertTrue(p.isDone());
		}
		
		assertEquals(2, bbqparty.getCompletedPhases().size());
		assertTrue(bbqparty.getCompletedPhases().contains(Phase.ENTERING_AND_SEATING));
		assertTrue(bbqparty.getCompletedPhases().contains(Phase.ORDERING_AND_EATING));
	}
	
	private Future<?> letParticipantCompleteAndWaitForEndOf(final Phase[] phases) {
		return participantPool.submit(new Runnable() {
			@Override
			public void run() {
				for (Phase phase: phases) {
					bbqparty.waitForEndOf(phase);
				}
			}
		});
	}
	
}
