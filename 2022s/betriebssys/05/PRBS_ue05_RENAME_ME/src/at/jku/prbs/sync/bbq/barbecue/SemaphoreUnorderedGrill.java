package at.jku.prbs.sync.bbq.barbecue;

import java.util.concurrent.Semaphore;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
* A thread-safe barbecue implementation that uses a Semaphore. Only ensures
* that a single participant is at the grill, but not necessarily the invited one.
* In addition, it is not guaranteed that only the participant that has approached
* the grill is the only one to also step away from it again.
*/
public class SemaphoreUnorderedGrill extends ChaoticGrill {
	
	private final Semaphore lock = new Semaphore(1);
	
	public SemaphoreUnorderedGrill(Participant firstParticipant) {
		super(firstParticipant);
	}

	@Override
	public void approachSafely() {		
		try {
			lock.acquire();
			
			super.approachSafely();			// run original (non thread-safe) code
		} catch (InterruptedException e) {
			lock.release();
		}
	}
	
	@Override
	public void stepAwaySafely() {		
		super.stepAwaySafely();		// run original (non thread-safe) code
		
		lock.release();
	}
}
