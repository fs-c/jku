package transport;

import transport.exceptions.CargoTooHeavyException;
import transport.exceptions.InvalidCargoTypeException;

public abstract class SolidCargoTransporter extends Transporter {
    public SolidCargoTransporter(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, currentLocation);
    }

    @Override
    public void load(Cargo cargo) throws CargoTooHeavyException, InvalidCargoTypeException {
        if (cargo.type() != Cargo.Type.SOLID) {
            throw new InvalidCargoTypeException("Transporter can only load solid cargo", this);
        }

        super.load(cargo);
    }
}
