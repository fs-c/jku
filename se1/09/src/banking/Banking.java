public class Banking {

	public static void main(String[] args) {
		Bank bank = new Bank();
		char ch;
		do {
			printMenu();
			ch = getOperation();

			try {
				switch (ch) {
				case 'a':
					createAccount(bank);
					break;
				case 'e':
					deposit(bank);
					break;
				case 'b':
					withdraw(bank);
					break;
				case 't':
					transfer(bank);
					break;
				case 'd':
					bank.printAccounts();
					break;
				case 'q':
					break;
				default:
					Out.println("Ungültige Operation");
					break;
				}
			} catch (IllegalArgumentException e) {
				Out.format("Ungültige Eingabe: %s%n", e.getMessage());
			}
		} while (ch != 'q');
	}

	private static void printMenu() {
		Out.println();
		Out.println("*********** Bankverwaltung ********");
		Out.println("Kunde+Konto anlegen ............. a");
		Out.println("Einzahlen ....................... e");
		Out.println("Beheben ......................... b");
		Out.println("Überweisen ...................... t");
		Out.println("Übersicht drucken ............... d");
		Out.println("Beenden ......................... q");
		Out.print("Welche Menuoption? [a|e|b|t|d|q]: ");
	}

	private static char getOperation() {
		char ch = Character.toLowerCase(In.readChar());
		In.readLine();
		return ch;
	}

	private static void createAccount(Bank bank) {
		printTitle("Kunde und Bankkonto anlagen");
		int accountId = 0;
		Customer customer = getCustomer();
		double overdraftLimit = getDouble("Überziehungsrahmen");

		try {
			accountId = bank.createAccount(customer, overdraftLimit);
		} catch (Bank.BankServiceException e) {
			Out.format("Fehler bei der Kontoanlegung: %s%n", e.getMessage());
		}

		printMessage("Anlegen", accountId >= 0);
	}

	private static void deposit(Bank bank) throws IllegalArgumentException {
		printTitle("Einzahlen");
		boolean success = false;
		int accountId = getInt("Kontonummer");
		double amount = getDouble("Einzahlungsbetrag");

		try {
			success = bank.deposit(accountId, amount);
		} catch (Account.NoSuchAccountException e) {
			Out.format("Fehler bei der Einzahlung: %s%n", e.getMessage());
		}

		printMessage("Einzahlen", success);
	}

	private static void withdraw(Bank bank) throws IllegalArgumentException {
		printTitle("Abheben");
		boolean success = false;
		int accountId = getInt("Kontonummer");
		double amount = getDouble("Abhebungsbetrag");

		try {
			success = bank.withdraw(accountId, amount);
		} catch (Account.AccountingException e) {
			Out.format("Fehler bei der Behebung: %s%n", e.getMessage());
		}

		printMessage("Abheben", success);
	}

	private static void transfer(Bank bank) throws IllegalArgumentException {
		printTitle("Überweisen");
		boolean success = false;
		int fromId = getInt("Von Kontonummer");
		int toId = getInt("Auf Kontonummer");
		double amount = getDouble("Betrag");

		try {
			success = bank.transfer(fromId, toId, amount);
		} catch (Account.AccountingException e) {
			Out.format("Fehler bei der Überweisung: %s%n", e.getMessage());
		}

		printMessage("Überweisen", success);
	}

	private static void printTitle(String text) {
		Out.println("*** " + text + " ***");
	}

	private static String getString(String text) {
		Out.print(text + ": ");
		return In.readLine();
	}

	private static double getDouble(String text) {
		Out.print(text + ": ");
		return In.readDouble();
	}

	private static int getInt(String text) {
		Out.print(text + ": ");
		return In.readInt();
	}

	private static Customer getCustomer() {
		String firstName = getString("Vorname");
		String lastName = getString("Nachname");
		String phoneNumber = getString("Telefonnummer");
		return new Customer(firstName, lastName, phoneNumber);
	}

	private static void printMessage(String operation, boolean success) {
		String message = success ? operation + " erfolgreich durchgeführt" : "Ungültige Operation";
		Out.println(message);
	}
}
