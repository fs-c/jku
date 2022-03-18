class BasicBanking {
	public static void main(String[] args) {
		Banking.createAccount(
			new Banking.Customer("Mustermann", "Max", "+43 1 555 666"),
			2000.0
		);

		Banking.createAccount(
			new Banking.Customer("Musterfrau", "Maximilia", "+43 1 777 888"),
			2200.0
		);

		Banking.printAccounts();
		Banking.printBalance();

		Banking.deposit(0, 2800.0);
		Banking.transfer(0, 1, 1300.0);

		Banking.printAccounts();
		Banking.printBalance();

		Banking.transfer(1, 0, 2000.0);

		Banking.printAccounts();
		Banking.printBalance();

		// This will fail
		Banking.withdraw(1, 2000.0);

		Banking.printAccounts();
		Banking.printBalance();
	}
}

class Banking {
	static final int MAX_ACCOUNTS = 100;

	private static int accountIndex = 0;
	private static Account[] accounts = new Account[Banking.MAX_ACCOUNTS];

	static class Customer {
		String lastName;
		String firstName;
		String phoneNumber;
	
		Customer(String lastName, String firstName, String phoneNumber) {
			this.lastName = lastName;
			this.firstName = firstName;
			this.phoneNumber = phoneNumber;
		}
	}

	private static class Account {
		Customer owner;
	
		int number;
		double balance;
		double overdraftLimit;
	
		Account(Customer owner, int number, double overdraftLimit) {
			this.owner = owner;
	
			this.number = number;
			this.overdraftLimit = overdraftLimit;
		}
	
		boolean withinLimit(double amount) {
			return (this.balance - amount) > (0.0 - this.overdraftLimit);
		}
	}

	static int createAccount(Customer owner, double overdraftLimit) {
		if (accountIndex >= Banking.MAX_ACCOUNTS)
			return -1;

		accounts[accountIndex] = new Account(owner, accountIndex,
			overdraftLimit);

		return accountIndex++;
	}

	static boolean deposit(int number, double amount) {
		if (accounts[number] == null)
			return false;

		accounts[number].balance += amount;

		return true;
	}

	static boolean withdraw(int number, double amount) {
		Account account = accounts[number];

		if (account == null)
			return false;

		if (!account.withinLimit(amount))
			return false;

		accounts[number].balance -= amount;

		return true;
	}

	static boolean transfer(int from, int to, double amount) {
		if (accounts[from] == null || accounts[to] == null)
			return false;
		
		if (!accounts[from].withinLimit(amount))
			return false;

		accounts[from].balance -= amount;
		accounts[to].balance += amount;

		return true;
	}

	static double getAccountBalance(int number) {
		if (accounts[number] == null)
			return 0;

		return accounts[number].balance;
	}

	static double getBalance() {
		double sum = 0;

		for (Account account : accounts) {
			if (account == null)
				continue;

			sum += account.balance;
		}
		
		return sum;
	}

	static void printBalance() {
		Out.println("");
		Out.println("--------------- Bilanz ----------------");
		Out.format("%.1f%n", getBalance());
		Out.println("---------------------------------------");
		Out.println("");
	}

	static void printAccounts() {
		Out.println("------------- Bankauszug --------------");

		for (Account account : accounts) {
			if (account == null)
				continue;

			Out.format("Kontonummer: %d%n", account.number);
			Out.format("Kontoinhaber: %s %s%n", account.owner.firstName,
				account.owner.lastName);
			Out.format("Kontostand: %.1f%n", account.balance);
			Out.format("Überziehungsrahmen: %.1f%n", account.overdraftLimit);

			Out.println("---------------------------------------");
		}
	}
}