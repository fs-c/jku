package at.jku.prbs.sync.bbq.barbecue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.participants.Participant;

/**
* A buggy implementation with no thread-safety.
*/
public class ChaoticGrill extends AbstractBarbecue {

	private AtomicInteger nrOfPeopleAtGrill = new AtomicInteger(0);

	private List<Dish> orders;
	private List<Dish> servedDishes;
	
	
	public ChaoticGrill(Participant firstParticipant) {
		super(firstParticipant);
		
		orders = new ArrayList<Dish>();
		servedDishes = new ArrayList<Dish>();
	}

	// not thread-safe
	@Override
	public void approachSafely() {
		changeAndPrintParticipantCount(+1, "after approaching");
	}
	
	// not thread-safe
	@Override
	public void stepAwaySafely() {
		changeAndPrintParticipantCount(-1, "after leaving");
	}
	
	private void changeAndPrintParticipantCount(int delta, String time) {
		Util.log(nrOfPeopleAtGrill.addAndGet(delta) + " participants at the grill " + time, 
				Participant.getCurrentParticipant().isPitmaster());
	}

	// not thread-safe
	@Override
	public void orderDish(Dish chosenDish) {
		if (!Participant.getCurrentParticipant().isPitmaster()) {
			orders.add(chosenDish);
			Util.log(chosenDish + " was put on the grill", true);
		} else
			Util.log(Participant.getCurrentParticipant() + " is not allowed to do that", true);
	}
	
	// not thread-safe
	@Override
	public Dish getDish() {
		Dish fetched = null;
		if (!Participant.getCurrentParticipant().isPitmaster()) {
			// always fetch the next dish that is ready
			fetched = orders.remove(0);		
			Util.log(fetched + " was taken away from the grill", true);
			servedDishes.add(fetched);
		} else
			Util.log(Participant.getCurrentParticipant() + " is not allowed to do that", true);

		return fetched;
	}
	
	// not thread-safe
	@Override
	public Map<Dish,Integer> getCountedServedDishes() {
		HashMap<Dish,Integer> countedDishes = new HashMap<Dish, Integer>();
		if (Participant.getCurrentParticipant().isPitmaster()) {
			for (Dish d:servedDishes) {
				int tmpCount = 0;
				if (countedDishes.get(d) != null)
					tmpCount = countedDishes.get(d);
				tmpCount++;
				countedDishes.put(d, tmpCount);
			}
		} else
			Util.log(Participant.getCurrentParticipant() + " is not allowed to do that", true);
			
		return countedDishes;
	}
}
