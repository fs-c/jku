package transport.exceptions;

import transport.Transporter;

public class InvalidCargoTypeException extends TransportException {
    public InvalidCargoTypeException(String message, Transporter transporter) {
        super(message, transporter);
    }
}
