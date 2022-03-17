package transport;

public abstract class Truck extends Transporter {
    public Truck(String name, int maxLoadWeight, int costPerKilometre, Cargo.Type[] allowedCargoTypes, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, allowedCargoTypes, canTraverseOcean, currentLocation);
    }

    @Override
    public double goTo(Location destination) {
        if (currentLocation.reachableOverland(destination))

        return super.goTo(destination);
    }
}
