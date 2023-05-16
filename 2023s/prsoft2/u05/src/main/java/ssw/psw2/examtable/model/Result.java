package ssw.psw2.examtable.model;

import javafx.beans.binding.Binding;
import javafx.beans.binding.Bindings;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.util.StringConverter;

public class Result {
	public static final int MIN_POINTS = 0;
	public static final int MAX_POINTS = 90;
	public static final int UNDEFINED = -1;
	
	private final Student student;
	private SimpleIntegerProperty points;
	private SimpleStringProperty grade;
	
	public Result(Student student) {
		super();
		this.student = student;
		this.points = new SimpleIntegerProperty(UNDEFINED);
		this.grade = new SimpleStringProperty();
	}

	public Student getStudent() {
		return student;
	}

	public String getStudentId() {
		return student.id.getValue();
	}

	public String getStudentLastName() {
		return student.name.getValue();
	}

	public String getStudentFirstName() {
		return student.firstName.getValue();
	}
	
	public int getPoints() {
		return points.get();
	}

	public IntegerProperty getPointsProperty() {
		return points;
	}
	
	public void setPoints(int points) {
		if ((points < MIN_POINTS || points > MAX_POINTS) && points != UNDEFINED) {
			throw new java.lang.IllegalArgumentException("Invalid point value"); 
		}

		this.points.set(points);
		this.grade.set(getGrade());
	}
	
	public String getGrade() {
		if(points.get() == UNDEFINED) {
			return "Kein Schein";
		}
		
		double percent = ((double)points.get()) / (MAX_POINTS);
		
		if(percent >= 0.875) {
			return "Sehr Gut";
		} else if(percent >= 0.75) {
			return "Gut";
		} else if(percent >= 0.625) {
			return "Befriedigend";
		} else if(percent >= 0.5) {
			return "Genügend";
		} else {
			return "Nicht Genügend";
		} 
	}
	
}
