package students;

public class Student extends Person {
    public enum Degree {
        BSC,
        MSC,
        PHD
    }

    public final String subject;
    public final Degree degree;

    public Student(String name, String subject, Degree degree) {
        super(name);
        this.subject = subject;
        this.degree = degree;
    }

    public void learn() {
        System.out.println("Student " + name + " is learning");
    }

    @Override
    public String toString() {
        return "Student{" +
                "name='" + name + '\'' +
                ", subject='" + subject + '\'' +
                ", degree=" + degree +
                '}';
    }
}
