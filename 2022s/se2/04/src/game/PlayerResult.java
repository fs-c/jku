package game;

public class PlayerResult {
    public static int N_CATEGORIES = 6;

    private final String name;
    private final int[] points = new int[N_CATEGORIES];

    PlayerResult(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public int getPoints(int category) {
        if (category >= 0 && category < points.length) {
            return points[category];
        } else {
            throw new IndexOutOfBoundsException("Points category " + category + " not valid");
        }
    }

    public boolean setPoints(int category, int p) {
        if ((category >= 0) && (category < N_CATEGORIES)) {
            points[category] = p;
            return true;
        } else {
            return false;
        }
    }
}
