package ssw.psw2.examtable.model;

import javafx.beans.property.SimpleStringProperty;

public class Student {

	public final SimpleStringProperty id;
	public final SimpleStringProperty firstName;
	public final SimpleStringProperty name;

	public Student(String id, String firstName, String name) {
		super();
		this.id = new SimpleStringProperty(id);
		this.firstName = new SimpleStringProperty(firstName);
		this.name = new SimpleStringProperty(name);
	}
}
