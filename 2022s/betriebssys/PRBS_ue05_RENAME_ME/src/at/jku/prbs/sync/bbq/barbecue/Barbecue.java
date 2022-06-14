package at.jku.prbs.sync.bbq.barbecue;

import java.util.Map;

import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * A simulated barbecue (i.e., a grill) that can be accessed by all participants.
 * Only one participant should use the barbecue at the same time.
 * If a participant has been scheduled to be next in line for the barbecue, 
 * only this participant is allowed to access it. Also, the dishes that can be 
 * placed on the barbecue are specified.
 */
public interface Barbecue {

	/**
	 * Lets the current thread (i.e., participant) approach the barbecue. 
	 * This needs to happen in a thread-safe manner, and ideally, 
	 * participants that cannot enter at the moment should wait for their 
	 * turn in a non-running state (i.e., busy waiting should be avoided!).
	 */
	void approach();
	
	/**
	 * Lets the current thread (i.e., participant) step away from the 
	 * barbecue. This needs to happen in a thread-safe manner, and 
	 * ideally, participants that wait for their turn are notified that 
	 * the barbecue is now free.
	 */
	void stepAway();

	/**
	 * Registers the given participant as the next one who may approach 
	 * the barbecue. This needs to happen in a thread-safe manner, and ideally, 
	 * participants that wait for their turn are notified that this change 
	 * has occurred.
	 */
	void setNextActive(Participant nextInLine);

	/**
	 * The current thread orders a dish.
	 * Only guests should be allowed to execute this method.
	 */
	void orderDish(Dish chosenDish);
	
	/**
	 * The current thread fetches a dish, hopefully but not necessarily 
	 * the one that was ordered. 
	 * Only guests should be allowed to execute this method.
	 */
	Dish getDish();
	
	/**
	 * Returns the consumption amount for each dish that was prepared 
	 * on the grill and consumed by the guests.
	 * Only the pitmaster should be allowed to execute this method.
	 */
	Map<Dish,Integer> getCountedServedDishes();
	
	/**
	 * Dishes to chose from 
	 */
	public enum Dish {
		BEEF(20),
		LAMB(15),
		CHICKEN(12),
		PORK(10),
		VEGETABLES(8);
		
		private int price;

		private Dish(int aPrice) {
			this.setPrice(aPrice);
		}
		
		public static Dish get(int index) {
			return values()[index];
		}
		
		public static int getCount() {
			return values().length;
		}

		public int getPrice() {
			return price;
		}

		public void setPrice(int price) {
			this.price = price;
		}
		
		public String toString() {
			return super.toString().toLowerCase();
		}
	}
}
