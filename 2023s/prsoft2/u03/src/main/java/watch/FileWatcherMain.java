package watch;

import java.io.IOException;
import java.util.Scanner;

public class FileWatcherMain {
  public static void main(String[] args) throws IOException {
    System.out.println("Terminate with ENTER!");

    // I had to change the path separator for linux compatibility, should work on windows as well
    // didn't find a properly os-independent path normalization method in the stdlib
    FileWatcher watcher = new FileWatcher("src/main/java/watch", "String");
    watcher.start();

    Scanner scanner = new Scanner(System.in);
    scanner.nextLine();

    watcher.terminate();

    System.out.println("Terminated");
  }
}
