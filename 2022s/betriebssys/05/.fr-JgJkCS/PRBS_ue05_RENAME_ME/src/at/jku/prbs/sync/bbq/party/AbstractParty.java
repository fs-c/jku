package at.jku.prbs.sync.bbq.party;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import at.jku.prbs.sync.bbq.BBQFactory;
import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.barbecue.Barbecue.Dish;
import at.jku.prbs.sync.bbq.participants.Guest;
import at.jku.prbs.sync.bbq.participants.Participant;
import at.jku.prbs.sync.bbq.participants.Pitmaster;
import at.jku.prbs.sync.bbq.participants.Guest.People;

/**
 * Base implementation for the BBQ party 
 */
public abstract class AbstractParty implements BBQParty {
	
	public static final int MAX_GUESTS_TO_PREP = 20;

	private static final Random RANDOM = new Random();

	private Set<Phase> completedPhases = EnumSet.noneOf(Phase.class);
	
	private List<Guest> guests = new ArrayList<Guest>();
	private Pitmaster chef = new Pitmaster(this);
	private final Barbecue theGrill = BBQFactory.newBarbecue(chef);
	
	private int availableSeats;
	
	
	public AbstractParty() {
		this.setAvailableSeats(BBQParty.MAX_SEATS);
		// randomly generate guests and their preferred dishes
		for (int i=0; i < MAX_GUESTS_TO_PREP; i++) {
			String name = People.values()[i % People.getCount()].toString();
			Dish aRandomDish = Dish.get(AbstractParty.RANDOM.nextInt(Dish.getCount()));
			guests.add(new Guest(this, aRandomDish, name));
		}
	}
	
	@Override
	public Barbecue getBarbecue() {
		return theGrill;
	}
	
	@Override
	public Collection<Guest> getGuests() {
		return guests;
	}
	
	@Override
	public Collection<Guest> getSeatedGuests() {
		ArrayList<Guest> seatedGuests = new ArrayList<Guest>();
		for (Guest g: getGuests())
			if (g.isGotSeat())
				seatedGuests.add(g);
		return seatedGuests;
	}
	
	@Override
	public Pitmaster getPitmaster() {
		return this.chef;
	}

	public int getAvailableSeats() {
		return availableSeats;
	}

	protected void setAvailableSeats(int availableSeats) {
		this.availableSeats = availableSeats;
	}

	@Override
	public void start() {
		for (Guest aGuest: getGuests()) {
			aGuest.start();
		}
		chef.start();
	}

	@Override
	public void waitForEndOf(Phase phase) {
		
		// the implementations only support waiting for the end of the currently running phase
		if (phase == getRunningPhase()) {
			try {
				waitForEndOfRunningPhase();		// call actual implementation of sub-classes
			} catch (Exception e) {
				throw new IllegalStateException(Participant.getCurrentParticipant() + " did not wait for the end of " + phase);
			}
		} else {
			throw new IllegalArgumentException("cannot leave the party (yet), must wait for the end of the currently running phase");
		}
	}
	
	// to be implemented in sub-classes
	protected abstract void waitForEndOfRunningPhase() throws Exception;
	
	protected void runningPhaseCompleted() {
		Phase runningPhase = getRunningPhase();
		Util.log("\n--- completed phase " + runningPhase + " ---\n", false);
		completedPhases.add(runningPhase);
	}
	
	@Override
	public Set<Phase> getCompletedPhases() {
		return Collections.unmodifiableSet(completedPhases);
	}
}
