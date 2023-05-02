package ssw.psw2.examtable.model;

public class Student {

	private final String id;
	private final String firstName;
	private final String name;

	public Student(String id, String firstName, String name) {
		super();
		this.id = id;
		this.firstName = firstName;
		this.name = name;
	}

	public String getID() {
		return id;
	}

	public String getFirstName() {
		return firstName;
	}

	public String getName() {
		return name;
	}
}
