package transport.exceptions;

import transport.Transporter;

public class TooHeavyException extends TransportException {
    public TooHeavyException(String message, Transporter transporter) {
        super(message, transporter);
    }
}
