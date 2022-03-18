public final class Account {
	private final int id;
	private final Customer owner;

	private double overdraftLimit;
	private double balance;

	static abstract class AccountingException extends Bank.BankServiceException {
		private int accountID;

		AccountingException(Bank bank, int accountID, String message) {
			super(bank, message);

			this.accountID = accountID;
		}

		int getAccountID() {
			return this.accountID;
		}
	}

	static class NoSuchAccountException extends AccountingException {
		NoSuchAccountException(Bank bank, int accountID) {
			super(bank, accountID, "No such account");
		}
	}

	static class OverdraftLimitReachedException extends AccountingException {
		private double amount;
		private double overdraftLimit;

		OverdraftLimitReachedException(Bank bank, int accountID, double amount, double overdraftLimit) {
			super(bank, accountID, "Overdraft limit reached");

			this.amount = amount;
			this.overdraftLimit = overdraftLimit;
		}
	}

	public Account(int id, Customer owner, double overdraftLimit) {
		this.id = id;
		this.owner = owner;
		this.overdraftLimit = overdraftLimit;
	}

	public int getId() {
		return id;
	}

	public Customer getOwner() {
		return owner;
	}

	public double getOverdraftLimit() {
		return overdraftLimit;
	}

	public double getBalance() {
		return balance;
	}

	public void increment(double amount) {
		balance += amount;
	}

	public void decrement(double amount) {
		balance -= amount;
	}

	public void print() {
		Out.println("Kontonummer: " + id);
		owner.print();
		Out.println(String.format("Kontostand: %.2f\nÜberziehungsrahmen: %.2f", balance, overdraftLimit));
	}
}
