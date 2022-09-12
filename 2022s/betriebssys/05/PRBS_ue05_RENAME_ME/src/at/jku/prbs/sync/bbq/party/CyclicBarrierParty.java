package at.jku.prbs.sync.bbq.party;

import java.util.concurrent.CyclicBarrier;

/**
 * An implementation that synchronizes the waiting of the participant
 * threads for (1.) a seat at the party using a synchronized block, 
 * and (2.) for each other at the end of each party phase by using 
 * CyclicBarrier.
 */
public class CyclicBarrierParty extends AbstractParty {
	
	// the index of the Phase that is currently running
	private int runningPhaseIdx = 0;
	
	// a re-usable barrier that synchronizes the actors for each Part
	// the run() method of the Runnable is run each time the barrier opens
	private CyclicBarrier barrier;

	
	public CyclicBarrierParty() {
		super();
		initBarrier(MAX_GUESTS_TO_PREP + 1);
	}
	
	private void initBarrier(int parties) {
		barrier = new CyclicBarrier(parties, new Runnable() {
			@Override
			public void run() {
				runningPhaseCompleted();
				runningPhaseIdx++;
				initBarrier(MAX_SEATS + 1);
			}
		});
	}
	
	@Override
	public Phase getRunningPhase() {
		return Phase.get(runningPhaseIdx);
	}

	@Override
	protected void waitForEndOfRunningPhase() throws Exception {
		// wait for other participants to arrive, or (in case the phase corresponding
		// to this round has already been completed) continue running
		barrier.await();
	}

	@Override
	public boolean requestSeat() {
		boolean seatAvailable = false;
		int seats = 0;
		synchronized(this) {
			if ((seats = getAvailableSeats()) > 0) {
				setAvailableSeats(seats - 1);
				seatAvailable = true;
			}
		}
		return seatAvailable;
	};
}
