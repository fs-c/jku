public final class Customer {
	private final String firstName;
	private final String lastName;
	private final String phoneNumber;

	public Customer(String firstName, String lastName, String phoneNumber) {
		this.firstName = firstName;
		this.lastName = lastName;
		this.phoneNumber = phoneNumber;
	}

	public String getFirstName() {
		return firstName;
	}

	public String getLastName() {
		return lastName;
	}

	public String getPhoneNumber() {
		return phoneNumber;
	}

	public void print() {
		Out.println(String.format("Kontoinhaber: %s %s\nTelefonnummer: %s", firstName, lastName, phoneNumber));
	}
}
