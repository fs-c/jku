package chat;

import java.io.IOException;
import java.net.Socket;

public class Client {
    public static void main(String[] args) {
        try (var socket = new Socket("localhost", 3000)) {
            System.out.println("[+] connected to server at " + socket.getInetAddress());

            new Handler(socket);
        } catch (IOException e) {
            System.out.println("[-] could not connect to server: " + e.getMessage());
        }
    }
}
