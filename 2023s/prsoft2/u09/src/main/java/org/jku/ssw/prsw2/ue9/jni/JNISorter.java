package org.jku.ssw.prsw2.ue9.jni;

public class JNISorter {

	static void loadLib() {
		System.loadLibrary("native-sort");
	}

	static {
		loadLib();
	}

	public static native void sort(int[][] c);

}
