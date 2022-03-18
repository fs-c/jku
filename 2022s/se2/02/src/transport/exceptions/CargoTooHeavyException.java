package transport.exceptions;

import transport.Transporter;

public class CargoTooHeavyException extends TransportException {
    public CargoTooHeavyException(String message, Transporter transporter) {
        super(message, transporter);
    }
}
