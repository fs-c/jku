package at.jku.prbs.sync.bbq.barbecue;

import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * A thread-safe barbecue implementation that uses the basic synchronization
 * primitives of Java: synchronized, wait(), notifyAll(). Ensures that only
 * the participant scheduled to be next is approaching the grill.  
 * Still it is not guaranteed that the one participant that has approached
 * the grill is the only one to also step away from it again.
 */

public class SynchronizedOrderedGrill extends ChaoticGrill {
		
	public SynchronizedOrderedGrill(Participant firstParticipant) {
		super(firstParticipant);
	}

	@Override
	public synchronized void setNextActive(Participant nextInLine) {
		super.setNextActive(nextInLine);		// run original (non thread-safe) code
	
		notifyAll();
	}
	
	@Override
	public synchronized void approachSafely() {
		while (Participant.getCurrentParticipant() != nextParticipant) {
			try {
				wait();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
				
		super.approachSafely();			// run original (non thread-safe) code
	}
	
	@Override
	public void stepAwaySafely() {
		super.stepAwaySafely();		// run original (non thread-safe) code
	}
}
