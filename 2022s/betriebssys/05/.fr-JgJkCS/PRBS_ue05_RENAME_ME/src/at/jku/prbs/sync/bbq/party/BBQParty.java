package at.jku.prbs.sync.bbq.party;

import java.util.Collection;
import java.util.Set;

import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.participants.Guest;
import at.jku.prbs.sync.bbq.participants.Pitmaster;

/**
 * Interface representing the simulated barbecue party, featuring the 
 * guests and the pitmaster that interact while the party is underway. 
 * The BBQ is split into phases, in which the participants should act in 
 * sync: after one phase is finished, all participants have to wait for 
 * every participant to finish the phase before continuing with the next 
 * one.
 */
public interface BBQParty {

	// the maximum number of seats available, i.e., the max number
	// of guests that are allowed to enter the party
	static final int MAX_SEATS = 10;
	
	
	Collection<Guest> getGuests();
	Collection<Guest> getSeatedGuests();		
	
	Pitmaster getPitmaster();
	Barbecue getBarbecue();				// the cooking device, not the party!
	
	// starts the party
	void start();
	
	// gets the currently running Phase
	Phase getRunningPhase();
	
	// lets the calling Participant wait until the end of the named Phase
	void waitForEndOf(Phase part);
	
	// determines which phases have already been completed
	Set<Phase> getCompletedPhases();
	
	/** 
	 * returns true if a guest is allowed to enter the bbq party depending
	 * on the number of available seats; if allowed, the remaining seats 
	 * are decremented
	 */
	boolean requestSeat();
	
	/**
	 * Phases of the BBQ party
	 */
	public enum Phase {
		ENTERING_AND_SEATING,
		ORDERING_AND_EATING,
		PAYING_AND_LEAVING;
		
		public static Phase get(int index) {
			return values()[index];
		}
		
		public static int getCount() {
			return values().length;
		}
	}
}
