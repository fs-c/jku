package at.jku.prbs.sync.bbq.barbecue;

import java.util.concurrent.locks.ReentrantLock;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
* A thread-safe barbecue implementation that uses a ReentrantLock. Only ensures
* that a single participant is at the grill, but not necessarily the invited one.
* In addition, it is not guaranteed that only the participant that has approached
* the grill is the only one to also step away from it again.
*/
public class LockedUnorderedGrill extends ChaoticGrill {
	
	private final ReentrantLock lock = new ReentrantLock();
	
	public LockedUnorderedGrill(Participant firstParticipant) {
		super(firstParticipant);
	}

	@Override
	public void approachSafely() {				
		lock.lock();
		
		super.approachSafely();			// run original (non thread-safe) code
	}
	
	@Override
	public void stepAwaySafely() {		
		super.stepAwaySafely();		// run original (non thread-safe) code
		
		lock.unlock();
	}
	
}
