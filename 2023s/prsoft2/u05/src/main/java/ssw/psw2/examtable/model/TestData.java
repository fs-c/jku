package ssw.psw2.examtable.model;

import java.util.ArrayList;
import java.util.List;

public class TestData {

	public static List<Result> createData() {
		List<Result> data = new ArrayList<>();
		
		Result r1 = new Result(new Student("k01245678", "Mia", "Musterstudentin"));
		r1.setPoints(90);
		data.add(r1);
		
		Result r2 = new Result(new Student("k01778901", "Max", "Mustermann"));
		r2.setPoints(87);
		data.add(r2);
		
		Result r3 = new Result(new Student("k01612345", "Fred", "Faul"));
		r3.setPoints(4);
		data.add(r3);
		
		Result r4 = new Result(new Student("k01612345", "Ulrike", "Unfertig"));
		data.add(r4);
		
		return data;
	}
}
