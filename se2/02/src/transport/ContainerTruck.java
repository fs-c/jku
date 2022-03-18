package transport;

import transport.exceptions.UnreachableByTransporterException;

public class ContainerTruck extends SolidCargoTransporter {
    public ContainerTruck(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, currentLocation);
    }

    @Override
    public double goTo(Location destination) throws UnreachableByTransporterException {
        if (!getCurrentLocation().reachableOverland(destination)) {
            throw new UnreachableByTransporterException("Trucks cannot cross oceans", this);
        }

        return super.goTo(destination);
    }
}
