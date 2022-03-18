package transport;

import transport.exceptions.CargoTooHeavyException;
import transport.exceptions.InvalidCargoTypeException;
import transport.exceptions.UnreachableByTransporterException;

public abstract class Transporter {
    private final String name;
    private final int maxLoadWeight;
    private final int costPerKilometre;

    private Cargo currentLoad;
    private Location currentLocation;

    public Transporter(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        if (currentLocation == null) {
            throw new IllegalArgumentException("Current location must not be null.");
        }

        this.name = name;
        this.maxLoadWeight = maxLoadWeight;
        this.costPerKilometre = costPerKilometre;
        this.currentLocation = currentLocation;
    }

    public String getName() {
        return name;
    }

    public int getMaxLoadWeight() {
        return maxLoadWeight;
    }

    public int getCostPerKilometre() {
        return costPerKilometre;
    }

    public Cargo getCurrentLoad() {
        return currentLoad;
    }

    public Location getCurrentLocation() {
        return currentLocation;
    }

    public double goTo(Location destination) throws UnreachableByTransporterException {
        double cost = currentLocation.getDistance(destination) * costPerKilometre;

        currentLocation = destination;

        return cost;
    }

    public void load(Cargo cargo) throws CargoTooHeavyException, InvalidCargoTypeException {
        if (currentLoad != null) {
            unload();
        }

        if (cargo.weight() > maxLoadWeight) {
            throw new CargoTooHeavyException("Attempted to load overweight cargo", this);
        }

        currentLoad = cargo;
    }

    public Cargo unload() {
        if (currentLoad == null) {
            throw new IllegalStateException();
        }

        Cargo load = currentLoad;

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
