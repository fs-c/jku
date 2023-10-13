package org.jku.ssw.prsw2.ue9.jni;

public class AdvancedJNISorter {
    static void loadLib() {
        System.load("/home/fsoc/Projects/jku/2023s/prsoft2/u09/src/main/java/org/jku/ssw/prsw2/ue9/jni/advanced-sort.so");
    }

    static {
        loadLib();
    }

    public static native void sort(int[][] c);
}
