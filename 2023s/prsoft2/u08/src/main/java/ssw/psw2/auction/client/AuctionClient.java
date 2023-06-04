package ssw.psw2.auction.client;

import org.glassfish.tyrus.client.ClientManager;

import javax.websocket.DeploymentException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;

import static ssw.psw2.auction.common.Constants.*;

public class AuctionClient {
    public static void main(String[] args) {
        final var client = ClientManager.createClient();

        try (var scanner = new Scanner(System.in)) {
            System.out.print("user: ");
            final var user = scanner.nextLine();

            final var uri = new URI("ws://" + HOST_NAME + ":" + PORT + AUCTION_BASE_PATH + AUCTION_ENDPOINT_PATH + "/" + user);
            final var latch = new CountDownLatch(1);

            client.connectToServer(new AuctionClientEndpoint(latch), uri);

            latch.await();
        } catch (URISyntaxException e) {
            System.err.println("couldn't construct server URI");
        } catch (DeploymentException e) {
            System.err.println("error connecting to server");
            e.printStackTrace();
        } catch (InterruptedException e) {
            // this is basically impossible, severe bug otherwise
            throw new RuntimeException();
        }
    }
}
