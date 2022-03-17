package transport;

public class CargoPlane extends Transporter {
    private static final int TAKEOFF_COST = 1000;
    private static final int LANDING_COST = 1000;

    public CargoPlane(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, new Cargo.Type[]{ Cargo.Type.SOLID }, canTraverseOcean, currentLocation);
    }

    @Override
    public double goTo(Location destination) {
        double travelCost = super.goTo(destination);

        return TAKEOFF_COST + travelCost + LANDING_COST;
    }
}
