package students;

public class Student extends Person {
	
	public Student(String name) {
		super(name); 
	}
	
	public void learn() {
		System.out.println("Student " + name + " is learning"); 
	}

}
