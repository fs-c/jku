public final class Bank {
	private static final int MAX_ACCOUNTS = 100;

	private final Account[] accounts = new Account[MAX_ACCOUNTS];
	private int count = 0;

	static class BankServiceException extends Exception {
		private Bank bank;

		BankServiceException(Bank bank, String message) {
			super(message);

			this.bank = bank;
		}

		Bank getBank() {
			return this.bank;
		}
	}

	public int createAccount(Customer owner, double overdraftLimit) throws BankServiceException {
		if (count == MAX_ACCOUNTS)
			throw new BankServiceException(this, "Maximum number of accounts reached");

		Account account = new Account(count, owner, overdraftLimit);
		accounts[count] = account;
		count++;
		return account.getId();
	}

	public boolean deposit(int accountId, double amount) throws Account.NoSuchAccountException, IllegalArgumentException {
		if (amount < 0)
			throw new IllegalArgumentException("Cannot deposit a negative number");

		Account account = findAccount(accountId);
		if (account == null)
			throw new Account.NoSuchAccountException(this, accountId);

		account.increment(amount);
		return true;
	}

	public boolean withdraw(int accountId, double amount) throws Account.AccountingException, IllegalArgumentException {
		if (amount < 0)
			throw new IllegalArgumentException("Cannot withdraw a negative number");

		Account account = findAccount(accountId);
		if (account == null)
			throw new Account.NoSuchAccountException(this, accountId);

		double limit = account.getOverdraftLimit();
		if (amount > (account.getBalance() + limit))
			throw new Account.OverdraftLimitReachedException(this, accountId, amount, limit);

		account.decrement(amount);
		return true;
	}

	public boolean transfer(int fromId, int toId, double amount) throws Account.AccountingException, IllegalArgumentException {
		if (amount < 0)
			throw new IllegalArgumentException("Cannot transfer a negative amount");

		Account from = findAccount(fromId);
		if (from == null)
			throw new Account.NoSuchAccountException(this, fromId);

		Account to = findAccount(toId);
		if (to == null)
			throw new Account.NoSuchAccountException(this, toId);

		double limit = from.getOverdraftLimit();
		if (amount > (from.getBalance() + limit))
			throw new Account.OverdraftLimitReachedException(this, fromId, amount, limit);

		from.decrement(amount);
		to.increment(amount);
		return true;
	}

	public double getAccountBalance(int accountId) {
		Account account = findAccount(accountId);
		return (account == null) ? 0 : account.getBalance();
	}

	public double getBalance() {
		double balance = 0.;
		for (int i = 0; i < count; i++) {
			balance += accounts[i].getBalance();
		}
		return balance;
	}

	public void printAccounts() {
		Out.println("---------- Bankauszug ----------");

		for (int i = 0; i < count; i++) {
			accounts[i].print();
			Out.println("--------------------------------");
		}
		Out.println(String.format("Bilanzsumme: %.2f", getBalance()));
		Out.println("--------------------------------");
	}

	private Account findAccount(int accountId) {
		for (int i = 0; i < count; i++) {
			Account account = accounts[i];
			if (account.getId() == accountId) {
				return account;
			}
		}
		return null;
	}
}
