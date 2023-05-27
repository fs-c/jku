package ssw.psw2.auction.client;

import ssw.psw2.auction.common.AuctionEvent;
import ssw.psw2.auction.common.AuctionEventCoders;

import javax.websocket.ClientEndpoint;
import javax.websocket.OnMessage;
import javax.websocket.OnOpen;
import javax.websocket.Session;
import java.io.IOException;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;

@ClientEndpoint(decoders = AuctionEventCoders.class, encoders = AuctionEventCoders.class)
public class AuctionClientEndpoint {
    private CountDownLatch latch;
    private Session session;

    private final Runnable startScanner = () -> {
        try (var scanner = new Scanner(System.in)) {
            while (true) {
                int bid = scanner.nextInt();
                // discard newline that nextInt didn't consume
                scanner.nextLine();

                if (bid == 0) {
                    return;
                }

                session.getAsyncRemote().sendObject(AuctionEvent.createNewBidEvent(null, bid, null));
            }
        } finally {
            if (session.isOpen()) {
                try {
                    session.close();
                } catch (IOException e) {
                    // well, this is awkward
                    e.printStackTrace();
                }
            }

            latch.countDown();
        }
    };

    public AuctionClientEndpoint(CountDownLatch latch) {
        this.latch = latch;
    }

    @OnOpen
    public void onOpen(Session session) {
        this.session = session;

        new Thread(startScanner).start();
    }

    @OnMessage
    public void onMessage(Session session, AuctionEvent e) {
        var message = switch (e.kind) {
            case START -> e.nameOfClient == null
                    ? String.format("joined auction for '%s', starting bid is %f", e.objectName, e.currentPrice)
                    : String.format("joined auction for '%s', current highest bid is %f ('%s')", e.objectName, e.currentPrice, e.nameOfClient);
            case CLIENT_JOINED -> String.format("'%s' joined", e.nameOfClient);
            // todo: maybe distinguish between leaving regularly and timeout
            case CLIENT_LEFT -> String.format("'%s' left", e.nameOfClient);
            case NEW_BID -> String.format("new highest bid is %f ('%s')", e.currentPrice, e.nameOfClient);
            case SOLD -> String.format("sold to '%s' for %f, auction has ended", e.nameOfClient, e.currentPrice);
            case CANCELLED -> "the auction was cancelled";
        };

        System.out.println(message);
    }
}
