package at.jku.prbs.sync.bbq.barbecue;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * A thread-safe barbecue implementation that uses atomic data types. 
 * Ensures that only the participant scheduled to be next is 
 * approaching the grill. Still it is not guaranteed that  
 * the one participant that has approached the grill is the only 
 * one to also step away from it again.
 */
public class AtomicOrderedGrill extends ChaoticGrill {

	public AtomicOrderedGrill(Participant firstParticipant) {
		// TODO: if needed, add code (possibly) before and after the super call
		super(firstParticipant);
	}

	@Override
	public void setNextActive(Participant nextInLine) {
		// TODO: add code (possibly) before and after the super call
		super.setNextActive(nextInLine);		// run original (non thread-safe) code
	}
	
	@Override
	public void approachSafely() {
		// TODO: add code (possibly) before and after the super call
		super.approachSafely();			// run original (non thread-safe) code
	}
	
	@Override
	public void stepAwaySafely() {
		// TODO: add code (possibly) before and after the super call
		super.stepAwaySafely();		// run original (non thread-safe) code
	}
}
