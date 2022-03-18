package transport.exceptions;

import transport.Transporter;

public class UnreachableByTransporterException extends TransportException {
    public UnreachableByTransporterException(String message, Transporter transporter) {
        super(message, transporter);
    }
}
