package transport.exceptions;

import transport.Transporter;

@SuppressWarnings("serial")
public abstract class TransportException extends Exception {
	private final Transporter transporter;

	public TransportException(String message, Transporter transporter) {
		super(message);
		this.transporter = transporter;
	}

	public Transporter getTransporter() {
		return transporter;
	}
}
