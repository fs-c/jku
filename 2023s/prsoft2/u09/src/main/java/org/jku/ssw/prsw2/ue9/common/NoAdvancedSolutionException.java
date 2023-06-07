package org.jku.ssw.prsw2.ue9.common;

/**
 * Marker exception thrown if no advanced sorting implementation was programmed.
 */
public class NoAdvancedSolutionException extends RuntimeException {

	private static final long serialVersionUID = 1L;

	public NoAdvancedSolutionException() {
		super("No advanced solution found.");
	}
}
