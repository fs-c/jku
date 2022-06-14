package at.jku.prbs.sync.bbq.barbecue;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * A thread-safe barbecue implementation that uses a ReentrantLock. 
 * Ensures that only the participant scheduled to be next is 
 * approaching the grill. Still it is not guaranteed that  
 * the one participant that has approached the grill is the only 
 * one to also step away from it again.
 */
public class LockedOrderedGrill extends ChaoticGrill {
	
	private final ReentrantLock lock = new ReentrantLock();
	private final Condition unoccupied = lock.newCondition();
		
	public LockedOrderedGrill(Participant firstParticipant) {
		// TODO: if needed, add code (possibly) before and after the super call
		super(firstParticipant);
	}

	@Override
	public void setNextActive(Participant nextInLine) {
		lock.lock();
				
		super.setNextActive(nextInLine);		// run original (non thread-safe) code
			
		unoccupied.signal();
				
		lock.unlock();
	}
	
	@Override
	public void approachSafely() {		
		lock.lock();
				
		try {
			while (Participant.getCurrentParticipant() != nextParticipant) {	
				unoccupied.await();
			}			
		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			lock.unlock();
		}
		
		super.approachSafely();			// run original (non thread-safe) code
	}
	
	@Override
	public void stepAwaySafely() {
		super.stepAwaySafely();		// run original (non thread-safe) code
	}
}
