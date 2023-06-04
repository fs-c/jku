package ssw.psw2.examtable.common;

import java.io.Serializable;

public class Student implements Serializable {

	private final String id;
	private final String firstName;
	private final String name;

	public Student(String id, String firstName, String name) {
		super();
		this.id = id;
		this.firstName = firstName;
		this.name = name;
	}

	public String getId() {
		return id;
	}

	public String getFirstName() {
		return firstName;
	}

	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		return "Student{" +
				"id='" + id + '\'' +
				", firstName='" + firstName + '\'' +
				", name='" + name + '\'' +
				'}';
	}
}
