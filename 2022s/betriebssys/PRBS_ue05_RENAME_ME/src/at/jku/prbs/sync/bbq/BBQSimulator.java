package at.jku.prbs.sync.bbq;

import at.jku.prbs.sync.bbq.party.BBQParty;

/**
 * Creates a new Barbecue simulation (using the factory pattern) and starts it.
 */
public class BBQSimulator {

	public static void main(String[] args) {
		BBQParty bbq = BBQFactory.newBBQParty();
		bbq.start();
	}

}
