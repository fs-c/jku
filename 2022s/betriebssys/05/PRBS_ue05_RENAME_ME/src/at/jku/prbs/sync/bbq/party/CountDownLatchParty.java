package at.jku.prbs.sync.bbq.party;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * An implementation that synchronizes the waiting of the participant
 * threads for (1.) a seat at the party using atomic data types, 
 * and (2.) for each other at the end of each party phase by using 
 * CountDownLatches.
 */
public class CountDownLatchParty extends AbstractParty {

	// the index of the Phase that is currently running
	private volatile int runningPhaseIdx = 0;
	
	// one CountDownLatch per Phase lets the arriving participant wait
	// until all participants have arrived and the latch is opened
	private CountDownLatch[] latches = new CountDownLatch[Phase.getCount()];

	private AtomicInteger availableAtomicSeats;
	
	
	public CountDownLatchParty() {
		super();
		availableAtomicSeats = new AtomicInteger(MAX_SEATS);
		// we further on ignore availableSeats member variable
		
		// create latches that let us wait for the respective number of participants (+ the chef)
		for (int i = 0; i < latches.length; i++) {
			if (i == 0)
				latches[i] = new CountDownLatch(MAX_GUESTS_TO_PREP + 1);
			else
				latches[i] = new CountDownLatch(MAX_SEATS + 1);
		}
	}
	
	@Override
	public Phase getRunningPhase() {
		return Phase.get(runningPhaseIdx);
	}

	@Override
	protected void waitForEndOfRunningPhase() throws Exception {
		CountDownLatch latch;
		
		synchronized (this) {
			latch = latches[runningPhaseIdx];
			
			// register the arrival of this participant
			latch.countDown();
		
			// if all participants have arrived, complete the current phase
			if (latch.getCount() == 0) {
				runningPhaseCompleted();
				runningPhaseIdx++;
			} 
		}
		
		// wait for other participants to arrive, or (in case the phase corresponding
		// to this latch has already been completed) continue running
		latch.await();
		
		// check for running phase progress to avoid race condition 
		synchronized (this) {
			if (runningPhaseIdx == 0)
				throw new IllegalStateException(Participant.getCurrentParticipant() + " skipped the barrier too soon!");
		}
	}

	@Override
	public boolean requestSeat() {
		return (availableAtomicSeats.decrementAndGet() >= 0);
	};
}
