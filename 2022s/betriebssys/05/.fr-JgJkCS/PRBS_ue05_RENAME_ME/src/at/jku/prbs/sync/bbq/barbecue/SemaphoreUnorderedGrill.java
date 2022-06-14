package at.jku.prbs.sync.bbq.barbecue;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
* A thread-safe barbecue implementation that uses a Semaphore. Only ensures
* that a single participant is at the grill, but not necessarily the invited one.
* In addition, it is not guaranteed that only the participant that has approached
* the grill is the only one to also step away from it again.
*/
public class SemaphoreUnorderedGrill extends ChaoticGrill {
	
	public SemaphoreUnorderedGrill(Participant firstParticipant) {
		// TODO: if needed, add code (possibly) before and after the super call
		super(firstParticipant);
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
