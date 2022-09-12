package at.jku.prbs.sync.bbq.party;

/**
 * A buggy implementation that does not synchronize the participants
 * whatsoever.
 */
public class ChaoticParty extends AbstractParty {

	@Override
	public Phase getRunningPhase() {
		// note: this way no Phase progress would be made! Bad idea!
		return Phase.ENTERING_AND_SEATING;		 
	}
	
	@Override
	protected void waitForEndOfRunningPhase() {
		
		// no actual synchronization, just sleeping which has a similar effect
		// but guarantees nothing, and may lead to race conditions
		try {
			Thread.sleep(100);
		} catch (InterruptedException e) { /* ignore */ }
	}

	// not thread-safe
	@Override
	public boolean requestSeat() {
		boolean allow = false;
		int curAvailableSeats;
		if ((curAvailableSeats = getAvailableSeats()) > 0) {
			try {
				Thread.sleep(100);		// even seating takes some time
			} catch (InterruptedException e) { /* ignore */ }			
			curAvailableSeats -= 1;
			allow = true;
			setAvailableSeats(curAvailableSeats);
		}
		return allow;
	}
}
