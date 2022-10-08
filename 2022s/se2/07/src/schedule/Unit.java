package schedule;

public enum Unit {

    Mon1(Day.MON, 1), Mon2(Day.MON, 2), Mon3(Day.MON, 3),
    Mon4(Day.MON, 4), Mon5(Day.MON, 5), Mon6(Day.MON, 6),

    Tue1(Day.TUE, 1), Tue2(Day.TUE, 2), Tue3(Day.TUE, 3),
    Tue4(Day.TUE, 4), Tue5(Day.TUE, 5), Tue6(Day.TUE, 6),

    Wen1(Day.WEN, 1), Wen2(Day.WEN, 2), Wen3(Day.WEN, 3),
    Wen4(Day.WEN, 4), Wen5(Day.WEN, 5), Wen6(Day.WEN, 6),

    Thu1(Day.THU, 1), Thu2(Day.THU, 2), Thu3(Day.THU, 3),
    Thu4(Day.THU, 4), Thu5(Day.THU, 5), Thu6(Day.THU, 6),

    Fri1(Day.FRI, 1), Fri2(Day.FRI, 2), Fri3(Day.FRI, 3),
    Fri4(Day.FRI, 4), Fri5(Day.FRI, 5), Fri6(Day.FRI, 6);

	
	private final Day day;
	private final int n;
	
	private Unit(Day day, int n) {
		this.day = day;
		this.n = n;
	}

	public Day getDay() {
		return day;
	}

	public int getN() {
		return n;
	}

	@Override
	public String toString() {
		return day.toString() + ":" + n;
	}
	
}
