package ssw.psw2.auction.server;

import org.glassfish.tyrus.server.Server;

import javax.websocket.DeploymentException;
import java.util.Scanner;

import static ssw.psw2.auction.common.Constants.*;

public class AuctionServer {
    // this is terrible but idk how to initialize the endpoint otherwise
    public static String objectName;
    public static int startingBid;
    public static Server server;

    public static void main(String[] args) {
        server = new Server(HOST_NAME, PORT, AUCTION_BASE_PATH, AuctionServerEndpoint.class);

        try (var scanner = new Scanner(System.in)) {
            System.out.print("object name: ");
            objectName = scanner.next();

            System.out.print("starting bid: ");
            startingBid = scanner.nextInt();
            // nextInt only reads the integer, not the '\n' that was sent to submit it, so discard it here
            scanner.nextLine();

            server.start();

            System.out.format("server started (object: '%s', starting bid: %d), press <return> to shut down\n", objectName, startingBid);

            scanner.nextLine();

            server.stop();
        } catch (DeploymentException e) {
            System.err.println("fatal deployment error:");
            e.printStackTrace();
        }
    }
}
