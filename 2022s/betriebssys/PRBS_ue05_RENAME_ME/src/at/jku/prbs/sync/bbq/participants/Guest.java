package at.jku.prbs.sync.bbq.participants;

import java.util.Random;

import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.barbecue.Barbecue.Dish;
import at.jku.prbs.sync.bbq.party.BBQParty;

/**
 * Thread representing a guest participating in the BBQ party with a certain
 * preference for a dish. 
 * The guest tries to enter the party, places an order, waits for the pitmaster
 * to announce the ordered dish to be ready, eats the dish and either is 
 * finished or enqueues again for a second helping, and finally pays and 
 * leaves the party.
 * Can be compared to other guests on the basis of the "fairness points".
 */
public class Guest extends Participant implements Comparable<Guest> {

	private static final int DEFAULT_FAIRNESS_POINTS = 100;

	
	private final Dish preferredDish;
	private final BBQParty party;
	
	private String guestName;
	private int fairnessPoints;
	private int spendings;
	private boolean gotSeat;
	private boolean stillHungry;
    
	private final Random random = new Random();
	
	
	public Guest(BBQParty aParty, Dish aDish, String name) {
		this.party = aParty;

		this.preferredDish = aDish;
		setGuestName(name);
		
		setGotSeat(false);
		setStillHungry(true);
		setPoints(DEFAULT_FAIRNESS_POINTS);
		setSpendings(0);
	}

	@Override
	public boolean isPitmaster() {
		return false;
	}
	
	public Dish getPreferredDish() {
		return preferredDish;
	}
	
	public int getPoints() {
		return fairnessPoints;
	}

	public void setPoints(int points) {
		this.fairnessPoints = points;
	}

	@Override
	public void run() {
		Barbecue theGrill = party.getBarbecue();
		
		Util.log(this + " waits to be seated", false);
		setGotSeat(party.requestSeat());
		party.waitForEndOf(BBQParty.Phase.ENTERING_AND_SEATING);
		
		if (isGotSeat()) {
			Util.log(this + " has managed to get in", false);
			
			boolean finished = false;
			boolean hasOrderedYet = false;
			while (!finished) {
				theGrill.approach();

				if (!hasOrderedYet) {
					Util.log(this + " is ordering "+ getPreferredDish(), false);
					theGrill.orderDish(getPreferredDish());
					
					hasOrderedYet = true;
				} else {
					Dish consumption = theGrill.getDish();
					// guest at least got something, so his fairness 
					// points can be reduced
					setPoints(getPoints()-(DEFAULT_FAIRNESS_POINTS/4));	
					
					Util.log(this + " got " + consumption, false);
					if (!consumption.equals(getPreferredDish()))
						Util.log(this + " is complaining!", false);
					
					setSpendings(getSpendings()+consumption.getPrice());
					
					finished = random.nextBoolean();					
					setStillHungry(!finished);
					hasOrderedYet = false;
				}
				
				theGrill.setNextActive(party.getPitmaster());
				theGrill.stepAway();
			}
			Util.log(this + " has finished eating", false);
			party.waitForEndOf(BBQParty.Phase.ORDERING_AND_EATING);
			
			Util.log(this + " is waiting for the bill", false);
			party.waitForEndOf(BBQParty.Phase.PAYING_AND_LEAVING);
			
		} else {
			Util.log(this + " was not allowed to enter the bbq party", false);
		}
		Util.log(this + " leaves the bbq party", false);
	}

	public boolean isGotSeat() {
		return gotSeat;
	}

	public void setGotSeat(boolean gotSeat) {
		this.gotSeat = gotSeat;
	}

	public boolean isStillHungry() {
		return stillHungry;
	}
	
	private void setStillHungry(boolean stillHungry) {
		this.stillHungry = stillHungry;
	}
	
	public int getSpendings() {
		return spendings;
	}

	private void setSpendings(int spendings) {
		this.spendings = spendings;
	}

	public String getGuestName() {
		return guestName;
	}

	public void setGuestName(String guestName) {
		this.guestName = guestName;
	}

	@Override
	public int compareTo(Guest anotherGuest) {
		return anotherGuest.getPoints() - this.getPoints();
	}
	
	@Override
	public String toString() {
		return getGuestName();
	}
	
	public enum People {
		Kant, Heidegger, Hume, Schopenhauer, Hegel, Wittgenstein, Schlegel,
		Nietzsche, Socrates, Mill, Plato, Aristotle, Hobbes, Descartes,
		Kierkegaard, Fichte, Smith, Bacon, Thales, Galilei;
		
		public static int getCount() {
			return values().length;
		}
	}
}

