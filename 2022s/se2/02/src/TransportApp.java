import inout.Out;
import transport.*;
import transport.exceptions.CargoTooHeavyException;
import transport.exceptions.InvalidCargoTypeException;
import transport.exceptions.TransportException;
import transport.exceptions.UnreachableByTransporterException;

public class TransportApp {
    private final static Location LINZ = new Location("Linz", 0, 0, Country.Austria);
    private final static Location PARIS = new Location("Paris", 300, 400, Country.France);
    private final static Location NY = new Location("NY", 8000, 0, Country.USA);

    private final static Cargo SOLID = new Cargo(Cargo.Type.SOLID, "solid15", 15000);
    private final static Cargo LIQUID = new Cargo(Cargo.Type.LIQUID, "liquid5", 5000);

    private static double getExpectedTravelCost(double costPerKilometre, double distance, double staticCosts) {
        return staticCosts + (costPerKilometre * distance);
    }

    private static void testPlane() {
        Transporter plane = new CargoPlane("plane", 20000, 1000, LINZ);

        double cost = 0;

        try {
            cost += plane.goTo(PARIS);
            Out.println("Plane flight to Paris ok: "+ plane);

            plane.load(SOLID);
            Out.println("Loaded solid on plane ok: "+ plane);

            cost += plane.goTo(NY);
            Out.println("Plane flight to NY ok: " + plane);

            plane.unload();
            Out.println("Plane unload ok: " + plane);

            double expectedCost = getExpectedTravelCost(plane.getCostPerKilometre(),
                    LINZ.getDistance(PARIS) + PARIS.getDistance(NY),
                    2 * (CargoPlane.TAKEOFF_COST + CargoPlane.LANDING_COST));

            if (expectedCost != cost) {
                Out.println(String.format("++ERROR++: Unexpected cost. Expected: %f, actual: %f", expectedCost, cost));
            }
        } catch (TransportException e) {
            Out.println("++ERROR++: Unexpected exception: "+ e);
        }

        try {
            plane.load(LIQUID);
            Out.println("++ERROR++: Expected exception but load liquid ok: " +
                    plane);
        } catch (TransportException e) {
            Out.println("Expected exception is: "+ e);
        }
    }

    private static void testTruck(boolean liquid) {
        Transporter truck = liquid
            ? new TankTruck("tankTruck", 20000, 1000, LINZ)
            : new ContainerTruck("containerTruck", 20000, 1000, LINZ);

        Cargo correctCargo = liquid ? LIQUID : SOLID;
        Cargo wrongCargo = liquid ? SOLID : LIQUID;

        double cost = 0;

        try {
            cost = truck.goTo(PARIS);
            Out.println("Truck drive to Paris ok: "+ truck);

            truck.load(correctCargo);
            Out.println("Truck loaded ok: "+ truck);

            truck.unload();
            Out.println("Truck unloaded ok: "+ truck);

            double expectedCost = getExpectedTravelCost(truck.getCostPerKilometre(),
                    LINZ.getDistance(PARIS), 0);

            if (expectedCost != cost) {
                Out.println(String.format("++ERROR++: Unexpected cost. Expected: %f, actual: %f", expectedCost, cost));
            }
        } catch (TransportException e) {
            Out.println("++ERROR++: Unexpected exception: "+ e);
        }

        try {
            truck.load(wrongCargo);
            Out.println("++ERROR++: Expected exception but load wrong cargo ok: " +
                    truck);
        } catch (TransportException e) {
            Out.println("Expected exception is: "+ e);
        }

        if (truck.getCurrentLoad() != null) {
            truck.unload();
        }

        try {
            truck.unload();
            Out.println("++ERROR++: Expected exception but unload empty ok: " +
                    truck);
        } catch (IllegalStateException e) {
            Out.println("Expected exception is: "+ e);
        }
    }

    public static void main(String[] args) {
        testPlane();
        testTruck(false);
        testTruck(true);
    }
}
