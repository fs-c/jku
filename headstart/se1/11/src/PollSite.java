class PollSite {
	long duration = 0;

	Area[] areas; 
	Voter[] voters;

	PollSite(int nHelpers, int nCabines, int nVoters, long duration) {
		voters = new Voter[nVoters];

		areas = new Area[] {
			new Area("lobby", Integer.MAX_VALUE),
			new Area("hall", nHelpers),
			new Area("booth", nCabines)
		};

		for (int i = 0; i < voters.length; i++)
			voters[i] = new Voter(i, areas[0], areas[1], areas[2]);
	}

	public void simulate() {
		long start = System.currentTimeMillis();

		start(voters);

		do {
			Thread.yield();
		} while (duration >= System.currentTimeMillis() - start);

		await(voters);
	}

	private void start(Thread[] threads) {
		for (int i = 0; i < threads.length; i++)
			threads[i].start();
	}

	private void await(Thread[] threads) {
		for (int i = 0; i < threads.length; i++) {
			while (threads[i].isAlive()) {
				try {
					threads[i].join();
				} catch (InterruptedException e) { /* Swallow */ }
			}
		}
	}

	public static void main(String[] args) {
		if (args.length == 0) {
			System.out.println("usage: java PollSite nOfHelpers nOfCabines nOfVoters durationMillis");
		
			return;
		}

		new PollSite(
			Integer.parseInt(args[0]), Integer.parseInt(args[1]),
			Integer.parseInt(args[2]), Integer.parseInt(args[3])
		).simulate();
	}
}

class Area {
	String name;
	int capacity = 0, currentVoters = 0;

	Area(String name, int capacity) {
		this.name = name;
		this.capacity = capacity;
	}

	public synchronized void enter(int id) throws InterruptedException {
		while (capacity < currentVoters) {
			debug(id + " blocked");

			wait();
		}

		currentVoters++;
		debug(id + " entered");
	}

	public synchronized void leave(int id) {
		if (currentVoters <= 0)
			return;

		currentVoters--;
		debug(id + " left");

		notify();
	}

	private void debug(String format, Object... args) {
		System.out.format("[%d] Area[%s](%d/%d): " + format + '\n',
			System.currentTimeMillis(), name, currentVoters, capacity, args);
	}
}

class Voter extends Thread {
	Area[] areas;
	int id = -1, currentArea = 0;

	Voter(int id, Area lobby, Area hall, Area booth) {
		this.id = id;
		this.areas = new Area[] {lobby, hall, booth};
	}

	public void run() {
		while (!Thread.currentThread().isInterrupted()) {
			boolean entered = false;
			Area area = areas[currentArea];

			debug("iterating");

			try {
				area.enter(id);
				entered = true;

				if (currentArea++ > 0)
					Thread.sleep((long) (Math.random() * 10_000));
			} catch (InterruptedException e) {
				Thread.currentThread().interrupt();
			} finally {
				if (!entered)
					break;

				area.leave(id);

				if (!Thread.currentThread().isInterrupted()) {
					try {
						Thread.sleep((long) (Math.random() * 5_000));
					} catch (InterruptedException e) {
						Thread.currentThread().interrupt();
					}
				}
			}

			if (currentArea >= 3) {
				while (isAlive()) {
					try {
						join();
					} catch (InterruptedException e) { /* Swallow */ };
				}
			}
		}
	}

	private void debug(String format, Object... args) {
		System.out.format("[%d] Voter[%d]: " + format + '\n',
			System.currentTimeMillis(), id, args);
	}
}
