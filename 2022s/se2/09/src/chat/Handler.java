package chat;

import inout.In;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

public class Handler {
    static private class SynchronizedConsole {
        public static synchronized void print(String s) {
            System.out.print(s);
        }

        public static synchronized String readln() {
            return In.readLine();
        }
    }

    private final Socket socket;

    private final BufferedReader reader;
    private final PrintWriter writer;

    public Handler(Socket s) throws IOException {
        socket = s;

        reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        writer = new PrintWriter(socket.getOutputStream());

        start();
    }

    private void start() {
        var readerThread = new Thread(() -> {
            SynchronizedConsole.print("[*] reader thread started\n");

            handleReading();

            System.out.println("[*] reader thread stopped");
        });

        var writerThread = new Thread(() -> {
            SynchronizedConsole.print("[*] writer thread started\n");

            handleWriting();

            // if we get here, the user typed "x" to exit the writing loop, send
            // a last message and close the output stream

            writer.println("bye");
            writer.flush();

            try {
                socket.shutdownOutput();
            } catch (IOException e) {
                System.out.println("[-] failed shutting down output: " + e.getMessage());
            }

            SynchronizedConsole.print("[*] writer thread stopped\n");
        });

        readerThread.start();
        writerThread.start();

        try {
            writerThread.join();

            // writer thread joined, continue listening for input until the other side also
            // closes the output stream

            readerThread.join();
        } catch (InterruptedException e) {
            System.out.println("[-] failed joining threads: " + e.getMessage());

            throw new RuntimeException(e);
        }

        // we're done, caller is responsible for cleaning up the socket
    }

    private void handleWriting() {
        boolean shouldContinue = true;

        while (shouldContinue) {
            // read a command from the user
            String command = In.readLine();

            if (command.length() == 0) {
                // if user just pressed enter, prompt them for input

                SynchronizedConsole.print("[<] ");
                String message = SynchronizedConsole.readln();

                writer.println(message);
                writer.flush();
            } else if (command.equalsIgnoreCase("x")) {
                // if user typed "x", exit the writing loop and thus the thread

                shouldContinue = false;
            }
        }
    }

    private void handleReading() {
        try {
            String message;

            // keep waiting for input until the other side closes the output stream
            while ((message = reader.readLine()) != null) {
                SynchronizedConsole.print("[>] " + message + "\n");
            }
        } catch (IOException e) {
            System.out.println("[-] failed reading from socket: " + e.getMessage());
        }
    }
}
