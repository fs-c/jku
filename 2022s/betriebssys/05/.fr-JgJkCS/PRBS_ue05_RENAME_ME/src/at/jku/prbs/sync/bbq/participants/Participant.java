package at.jku.prbs.sync.bbq.participants;

/**
 * Active component of the bbq party, performing actions during the party.
 */
public abstract class Participant extends Thread{

	// Singleton to use when the Participant is not known (or unimportant)
	public static final Participant UNKNOWN = new Participant() {
		@Override public String toString() { return "unknown participant"; }
		@Override public boolean isPitmaster() { return false; }
	};
	
	// Determines the current participant via the currently running thread
	public static Participant getCurrentParticipant() {
		Thread currentThread = Thread.currentThread();
		if (currentThread instanceof Participant) {
			return (Participant) currentThread;
		} else {
			return UNKNOWN;
		}
	}
	
	// to be implemented in sub-classes
	public abstract boolean isPitmaster();
		
}
