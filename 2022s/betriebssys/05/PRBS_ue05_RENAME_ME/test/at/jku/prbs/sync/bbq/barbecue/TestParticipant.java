package at.jku.prbs.sync.bbq.barbecue;

import java.util.Random;
import java.util.concurrent.CountDownLatch;

import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.participants.Participant;

public class TestParticipant extends Participant {

	protected static final Random RANDOM = new Random();
	
	
	private final int nr;
	private final Participant invitee;
	
	private final Barbecue grill;
	private volatile boolean atGrill = false;
	
	private CountDownLatch continueLatch = new CountDownLatch(1);

	
	TestParticipant(int nr, Barbecue grill, Participant invitee) {
		this.nr = nr;
		this.grill = grill;
		this.invitee = invitee;
	}
	
	public boolean isAtGrill() {
		return atGrill;
	}
	
	@Override
	public boolean isPitmaster() {
		return false;
	}
	
	@Override
	public void run() {
		try {
			Thread.sleep(RANDOM.nextInt(100));
		} catch (InterruptedException e1) { /* ignore */ }
		
		grill.approach();
		atGrill = true;
		
		try {
			continueLatch.await();
			
			if (invitee != null) {
				grill.setNextActive(invitee);
			}
			
		} catch (InterruptedException e) {
			throw new RuntimeException(this + " interrupted while waiting to continue");
		} finally {
			grill.stepAway();
			atGrill = false;
		}
	}
	
	public void continueAndLeave() {
		continueLatch.countDown();
	}

	@Override
	public String toString() {
		return "(test participant #" + nr + ")";
	}

}