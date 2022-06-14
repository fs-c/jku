package at.jku.prbs.sync.bbq;

import at.jku.prbs.sync.bbq.barbecue.AtomicOrderedGrill;
import at.jku.prbs.sync.bbq.barbecue.Barbecue;
import at.jku.prbs.sync.bbq.barbecue.ChaoticGrill;
import at.jku.prbs.sync.bbq.barbecue.LockedOrderedGrill;
import at.jku.prbs.sync.bbq.barbecue.LockedUnorderedGrill;
import at.jku.prbs.sync.bbq.barbecue.SemaphoreOrderedGrill;
import at.jku.prbs.sync.bbq.barbecue.SemaphoreUnorderedGrill;
import at.jku.prbs.sync.bbq.barbecue.SynchronizedOrderedGrill;
import at.jku.prbs.sync.bbq.participants.Participant;
import at.jku.prbs.sync.bbq.party.BBQParty;
import at.jku.prbs.sync.bbq.party.ChaoticParty;
import at.jku.prbs.sync.bbq.party.CountDownLatchParty;
import at.jku.prbs.sync.bbq.party.CyclicBarrierParty;
import at.jku.prbs.sync.bbq.party.PhaserParty;

public class BBQFactory {
	public static BBQParty newBBQParty() {
		BBQParty parties[] = { new ChaoticParty(), new PhaserParty(),
				new CyclicBarrierParty(), new CountDownLatchParty() };
		return parties[0];
	}

	public static Barbecue newBarbecue(Participant firstParticipant) {
		Barbecue bbqs[] = { new ChaoticGrill(firstParticipant),
				new LockedUnorderedGrill(firstParticipant),
				new SemaphoreUnorderedGrill(firstParticipant),
				new SynchronizedOrderedGrill(firstParticipant),
				new LockedOrderedGrill(firstParticipant),
				new SemaphoreOrderedGrill(firstParticipant),
				new AtomicOrderedGrill(firstParticipant) };
		return bbqs[0];
	}
}
