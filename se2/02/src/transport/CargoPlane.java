package transport;

import transport.exceptions.UnreachableByTransporterException;

public class CargoPlane extends SolidCargoTransporter {
    // Assuming that takeoff and landing cost is independent of the actual plane,
    // like static fees for using a runway or something like that
    // (Public for the tests in main, not necessary otherwise.)
    public static final int TAKEOFF_COST = 1000;
    public static final int LANDING_COST = 1000;

    public CargoPlane(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, currentLocation);
    }

    @Override
    public double goTo(Location destination) throws UnreachableByTransporterException {
        double travelCost = super.goTo(destination);

        return TAKEOFF_COST + travelCost + LANDING_COST;
    }
}
