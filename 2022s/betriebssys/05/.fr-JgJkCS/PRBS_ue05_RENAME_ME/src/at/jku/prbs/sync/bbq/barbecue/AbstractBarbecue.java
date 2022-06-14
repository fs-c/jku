package at.jku.prbs.sync.bbq.barbecue;

import at.jku.prbs.sync.bbq.Util;
import at.jku.prbs.sync.bbq.participants.Participant;

/**
 * Basic implementation of a barbecue, i.e., a grill. The approaching 
 * and stepping away from the grill is wrapped, and the respective 
 * thread-safe methods have to be implemented by concrete 
 * implementations. The method for setting/inviting the next participant that
 * is allowed to approach the barbecue may have to be overridden as well.
 * Also, some methods from the Barbecue interface may need to be implemented
 * by the subclasses.
 */
public abstract class AbstractBarbecue implements Barbecue {

	protected volatile Participant nextParticipant;
	
	
	public AbstractBarbecue(Participant firstOnGrill) {
		this.nextParticipant = firstOnGrill;
	}
	
	@Override
	public void setNextActive(Participant nextInLine) {
		nextParticipant = nextInLine;
		Participant inviter = Participant.getCurrentParticipant();
		Util.log(inviter + " sets the next active participant to " + nextInLine, inviter.isPitmaster());
	}
	
	@Override
	public void approach() {
		Participant nextActive = Participant.getCurrentParticipant();
		Util.log(nextActive + " waiting to approach the grill", nextActive.isPitmaster());
		approachSafely();
		Util.log(nextActive + " has approached the grill", nextActive.isPitmaster());
	}

	@Override
	public void stepAway() {
		Participant nextActive = Participant.getCurrentParticipant();
		Util.log(nextActive + " is about to step away from the grill", nextActive.isPitmaster());
		stepAwaySafely();
		Util.log(nextActive + " has left the grill", nextActive.isPitmaster());
	}

	// to be implemented in sub-classes
	protected abstract void approachSafely();
	
	// to be implemented in sub-classes
	protected abstract void stepAwaySafely();
}
