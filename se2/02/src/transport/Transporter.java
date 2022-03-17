package transport;

import transport.exceptions.InvalidCargoTypeException;
import transport.exceptions.TooHeavyException;

public abstract class Transporter {
    private final String name;
    private final int maxLoadWeight;
    private final int costPerKilometre;
    private final Cargo.Type[] allowedCargoTypes;
    private final boolean canTraverseOcean;

    private Location currentLocation;
    private Cargo currentLoad;

    public Transporter(String name, int maxLoadWeight, int costPerKilometre, Cargo.Type[] allowedCargoTypes, boolean canTraverseOcean, Location currentLocation) {
        if (currentLocatiom == null) {
            // Error or something
        }

        this.name = name;
        this.maxLoadWeight = maxLoadWeight;
        this.costPerKilometre = costPerKilometre;
        this.allowedCargoTypes = allowedCargoTypes;
        this.canTraverseOcean = canTraverseOcean;
        this.currentLocation = currentLocation;
    }

    public double goTo(Location destination) {
        if (!canTraverseOcean && !currentLocation.reachableOverland(destination)) {
            throws
        }

        double cost = currentLocation.getDistance(destination) * costPerKilometre;

        currentLocation = destination;

        return cost;
    }

    public void load(Cargo cargo) throws TooHeavyException, InvalidCargoTypeException {
        if (currentLoad != null) {
            unload();
        }

        if (cargo.weight() > maxLoadWeight) {
            throw new TooHeavyException("Attempted to load overweight cargo", this);
        }

        for (Cargo.Type allowedCargoType : allowedCargoTypes) {
            if (allowedCargoType == cargo.type()) {
                currentLoad = cargo;

                return;
            }
        }

        throw new InvalidCargoTypeException("Invalid cargo type", this);
    }

    public Cargo unload() {
        Cargo load = currentLoad;

        if (load == null) {
            throw new IllegalStateException();
        }

        currentLoad = null;

        return load;
    }

    @Override
    public String toString() {
        return "Transporter{" +
                "name='" + name + '\'' +
                ", maxLoadWeight=" + maxLoadWeight +
                ", costPerKilometre=" + costPerKilometre +
                ", currentLocatiom=" + currentLocation +
                ", currentLoad=" + currentLoad +
                '}';
    }
}
