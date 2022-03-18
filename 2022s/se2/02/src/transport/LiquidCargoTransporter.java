package transport;

import transport.exceptions.CargoTooHeavyException;
import transport.exceptions.InvalidCargoTypeException;

public abstract class LiquidCargoTransporter extends Transporter {
    public LiquidCargoTransporter(String name, int maxLoadWeight, int costPerKilometre, Location currentLocation) {
        super(name, maxLoadWeight, costPerKilometre, currentLocation);
    }

    @Override
    public void load(Cargo cargo) throws CargoTooHeavyException, InvalidCargoTypeException {
        if (cargo.type() != Cargo.Type.LIQUID) {
            throw new InvalidCargoTypeException("Transporter can only load liquid cargo", this);
        }

        super.load(cargo);
    }
}
