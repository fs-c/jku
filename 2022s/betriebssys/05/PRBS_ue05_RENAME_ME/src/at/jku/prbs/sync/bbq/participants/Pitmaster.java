package at.jku.prbs.sync.bbq.participants;

import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.party.BBQParty;

/**
 * Thread representing the person in charge for the barbecue, i.e., the pitmaster. 
 * Welcomes the guests, asks them for their choice of dish and collects the bills. 
 * Whenever the pitmaster performs an action, he/she does so at the grill.
 */
public class Pitmaster extends Participant {
	
	private final BBQParty party;
	
	
	public Pitmaster(BBQParty aParty) {
		this.party = aParty;
	}
	
	@Override
	public boolean isPitmaster() {
		return true;
	}

	@Override
	public void run() {
		Barbecue theGrill = party.getBarbecue();
		
		theGrill.approach();
		Util.log(this + " is welcoming the guests...", true);
		theGrill.stepAway();
		party.waitForEndOf(BBQParty.Phase.ENTERING_AND_SEATING);

		boolean finished = false;
		while (!finished) {
			boolean peopleStillInLine = false;
			for (Guest aGuest: party.getSeatedGuests()) {
				theGrill.approach();
				Util.log(this + " asks " + aGuest+ " for his order/anything else", true);
				if (aGuest.isStillHungry()) {
					theGrill.setNextActive(aGuest);
					peopleStillInLine = true;
				} else
					theGrill.setNextActive(this);		// skipping the guest
				theGrill.stepAway();
			}
			finished = !peopleStillInLine;
		}
		party.waitForEndOf(BBQParty.Phase.ORDERING_AND_EATING);
		
		theGrill.approach();
		Util.log(this + " is starting to hand out the bills to the guests", true);
		int totalRevenue = 0;
		for (Guest aGuest: party.getSeatedGuests()) {		// this was originally calling getGuests(); not ideal!
			int bill = aGuest.getSpendings();
			totalRevenue += bill;
			Util.log(this + " collects " + bill + " from " + aGuest, true);
		}
		theGrill.stepAway();
		party.waitForEndOf(BBQParty.Phase.PAYING_AND_LEAVING);
		
		theGrill.approach();
		Util.log(this + " closes the cash desk and counts the revenue.", true);
		Util.log("total party revenue: " + totalRevenue, true);
		Util.log("total consumption: " + theGrill.getCountedServedDishes(), true);
		theGrill.stepAway();
	}
	
	@Override
	public String toString() {
		return "The pitmaster";
	}
}
