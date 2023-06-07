package org.jku.ssw.prsw2.ue9.common;

/**
 * Marker exception thrown if no jni sorting library was loaded.
 */
public class JNISolutionNotImplementedException extends RuntimeException {

	private static final long serialVersionUID = 1L;

	public JNISolutionNotImplementedException() {
		super("No JNI sorter library was loaded.");
	}
}
