package at.jku.prbs.sync.bbq.party;

import java.util.concurrent.Phaser;
import java.util.concurrent.locks.ReentrantLock;

/**
 * An implementation that synchronizes the waiting of the participant
 * threads for (1.) a seat at the party using a ReentrantLock, 
 * and (2.) for each other at the end of each party phase by using 
 * Phaser.
 */
public class PhaserParty extends AbstractParty {
	
	// re-usable barriers that synchronize the participants; for each Phase
	// the onAdvance() method is run each time the barrier opens; 
	// the total number of participants at the entrance is the maximum of guests + 1 pitmaster 
	private Phaser phaserEntrance;
	// the total number on the party is the number of seats + 1 pitmaster 
	private Phaser phaserInside;
	
	// a locking primitive with fair queuing
	private ReentrantLock seatLock = new ReentrantLock(true);
	

	public PhaserParty (){
		super();
		initBarrier();
	}
	
	private void initBarrier() {
		phaserEntrance = new Phaser(MAX_GUESTS_TO_PREP+1) {
			@Override
			protected boolean onAdvance(int phase, int registeredParties) {
				runningPhaseCompleted();
				return true;			// phaser will not be reused
			}
		};
		phaserInside = new Phaser(MAX_SEATS+1) {
			@Override
			protected boolean onAdvance(int phase, int registeredParties) {
				runningPhaseCompleted();
				return false;			// phaser will be reused
			}
		};
	}
	
	@Override
	public Phase getRunningPhase() {
		// we need to manage two phaser objects - the entrance phaser and the phaser inside the party. 
		int phaseNr; 
		if (phaserEntrance.isTerminated())
			phaseNr = phaserInside.getPhase() + 1;
		else
			phaseNr = phaserEntrance.getPhase();			// or 0...
		return Phase.get(phaseNr);	// the phaser keeps track of the rounds internally
	}

	@Override
	protected void waitForEndOfRunningPhase() throws Exception {
		// wait for other participants to arrive, or (in case the phase corresponding
		// to this round has already been completed) continue running
		if (!phaserEntrance.isTerminated()) {
			phaserEntrance.arriveAndAwaitAdvance();			
		} else {
			phaserInside.arriveAndAwaitAdvance();
		}
	}

	@Override
	public boolean requestSeat() {
		boolean seatAvailable = false;
		int seats = 0;
		seatLock.lock();						// lock access to member variable
		try {
			if ((seats = getAvailableSeats()) > 0) {
				setAvailableSeats(seats - 1);
				seatAvailable = true;
			}
		} finally {
			seatLock.unlock();					// unlock access to member variable
		}
		return seatAvailable;
	}
}
