package chat;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class Server {
    public static void main(String[] args) {
        try (var server = new ServerSocket(3000)) {
            System.out.println("[+] started server at "
                    + server.getInetAddress() + ":" + server.getLocalPort());

            while (true) {
                try (Socket socket = server.accept()) {
                    System.out.println("[+] accepted connection from " + socket.getInetAddress());

                    new Handler(socket);

                    System.out.println("[*] closed connection from " + socket.getInetAddress());
                } catch (IOException e) {
                    System.out.println("[-] error accepting connection: " + e.getMessage());
                }
            }
        } catch (IOException e) {
            System.out.println("[-] could not start server");
        }
    }
}
