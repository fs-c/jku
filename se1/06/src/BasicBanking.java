class BasicBanking {
	public static void main(String[] args) {
		Banking bank = new Banking();

		bank.createAccount(new Customer("Mustermann", "Max", "+43 1 555 666"), 2000.0);
		bank.createAccount(new Customer("Musterfrau", "Maximilia", "+43 1 777 888"), 2200.0);

		bank.printAccounts();
		bank.printBalance();

		bank.deposit(0, 2800.0);
		bank.transfer(0, 1, 1300.0);

		bank.printAccounts();
		bank.printBalance();

		bank.transfer(1, 0, 2000.0);

		bank.printAccounts();
		bank.printBalance();

		// This will fail
		bank.withdraw(1, 2000.0);

		bank.printAccounts();
		bank.printBalance();
	}
}

class Customer {
	String lastName;
	String firstName;
	String phoneNumber;

	Customer(String last, String first, String phone) {
		this.lastName = last;
		this.firstName = first;
		this.phoneNumber = phone;
	}
}

class Account {
	Customer owner;

	int number;
	double balance;
	double overdraft;

	Account(Customer owner, int number, double overdraft) {
		this.owner = owner;

		this.number = number;
		this.overdraft = overdraft;
	}

	public boolean withinLimit(double amount) {
		return (this.balance - amount) > (0.0 - this.overdraft);
	}
}

class Banking {
	public static final int MAX_ACCOUNTS = 100;

	private int accountIndex = 0;
	private Account[] accounts = new Account[Banking.MAX_ACCOUNTS];

	int createAccount(Customer owner, double overdraftLimit) {
		if (accountIndex >= Banking.MAX_ACCOUNTS)
			return -1;

		accounts[accountIndex] = new Account(owner, accountIndex,
			overdraftLimit);

		return accountIndex++;
	}

	boolean deposit(int number, double amount) {
		if (accounts[number] == null)
			return false;

		accounts[number].balance += amount;

		return true;
	}

	boolean withdraw(int number, double amount) {
		Account account = accounts[number];

		if (account == null)
			return false;

		if (!account.withinLimit(amount))
			return false;

		accounts[number].balance -= amount;

		return true;
	}

	boolean transfer(int from, int to, double amount) {
		if (accounts[from] == null || accounts[to] == null)
			return false;
		
		if (!accounts[from].withinLimit(amount))
			return false;

		accounts[from].balance -= amount;
		accounts[to].balance += amount;

		return true;
	}

	double getAccountBalance(int number) {
		if (accounts[number] == null)
			return 0;

		return accounts[number].balance;
	}

	double getBalance() {
		double sum = 0;

		for (Account account : accounts) {
			if (account == null)
				continue;

			sum += account.balance;
		}
		
		return sum;
	}

	void printBalance() {
		Out.println("");
		Out.println("--------------- Bilanz ----------------");
		Out.format("%.1f%n", this.getBalance());
		Out.println("---------------------------------------");
		Out.println("");
	}

	void printAccounts() {
		Out.println("------------- Bankauszug --------------");

		for (Account account : accounts) {
			if (account == null)
				continue;

			Out.format("Kontonummer: %d%n", account.number);
			Out.format("Kontoinhaber: %s %s%n", account.owner.firstName,
				account.owner.lastName);
			Out.format("Kontostand: %.1f%n", account.balance);
			Out.format("Überziehungsrahmen: %.1f%n", account.overdraft);

			Out.println("---------------------------------------");
		}
	}
}