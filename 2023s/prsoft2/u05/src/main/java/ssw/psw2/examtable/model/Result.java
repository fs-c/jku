package ssw.psw2.examtable.model;

public class Result {
	public static final int MIN_POINTS = 0;
	public static final int MAX_POINTS = 90;
	public static final int UNDEFINED = -1;
	
	private final Student student; 
	private int points;
	
	public Result(Student student) {
		super();
		this.student = student;
		this.points = UNDEFINED;
	}

	public Student getStudent() {
		return student;
	}
	
	public int getPoints() {
		return points; 
	}
	
	public void setPoints(int points) {
		if ((points < MIN_POINTS || points > MAX_POINTS) && points != UNDEFINED) {
			throw new java.lang.IllegalArgumentException("Invalid point value"); 
		}
		this.points = points;
	}
	
	public String getGrade() {
		if(points == UNDEFINED) {
			return "Kein Schein";
		}
		
		double percent = ((double)points) / (MAX_POINTS);
		
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
