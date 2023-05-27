package ssw.psw2.auction.server;

import ssw.psw2.auction.common.AuctionEvent;
import ssw.psw2.auction.common.AuctionEventCoders;

import javax.websocket.*;
import javax.websocket.server.PathParam;
import javax.websocket.server.ServerEndpoint;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Map;
import java.util.concurrent.*;

import static ssw.psw2.auction.common.Constants.*;

// todo: could use Configurator to change how ServerEndpoint is constructed

@ServerEndpoint(value = AUCTION_ENDPOINT_PATH + "/{user}", encoders = AuctionEventCoders.class, decoders = AuctionEventCoders.class)
public class AuctionServerEndpoint {
    private static final Map<String, Session> sessions = new ConcurrentHashMap<>();
    private static final Map<String, Long> sessionPongTimes = new ConcurrentHashMap<>();

    private static final long TIMEOUT_TIME_MS = 2000;

    private static double currentHighestBid = AuctionServer.startingBid;
    private static String currentHighestBidder;

    private static ScheduledFuture<?> checkConnectionsFuture = null;
    private static final ScheduledExecutorService scheduler = Executors.newScheduledThreadPool(1);

    private final Runnable checkConnections = () -> {
        System.out.println("checking connections");

        var dummy = ByteBuffer.allocate(1);

        sessions.forEach((user, session) -> {
            try {
                // send a ping...
                session.getAsyncRemote().sendPing(dummy);

                // ...and check whether the previously sent ping received a response in time
                if (sessionPongTimes.get(user) + TIMEOUT_TIME_MS < System.currentTimeMillis()) {
                    System.out.format("closing connection for user '%s'\n", user);

                    // consider the connection lost if not
                    session.close();
                    // not sure why it's necessary to manually call close handler here
                    onClose(session, null, user);
                }
            } catch (IOException e) {
                System.out.format("connection check failed for '%s'\n", user);
            }
        });
    };

    @OnOpen
    public void onOpen(Session session, @PathParam("user") String user) {
        if (sessions.containsKey(user)) {
            try {
                session.close(new CloseReason(CloseReason.CloseCodes.CANNOT_ACCEPT, "duplicate user"));
            } catch (IOException e) {
                e.printStackTrace();

                // we don't want the session, but we couldn't close it... let's just ignore the problem
                return;
            }
        }

        broadcast(AuctionEvent.createClientJoinedEvent(user));

        session.getAsyncRemote().sendObject(AuctionEvent.createStartEvent(AuctionServer.objectName, currentHighestBid, currentHighestBidder));

        sessions.put(user, session);
        sessionPongTimes.put(user, System.currentTimeMillis());

        if (checkConnectionsFuture == null) {
            checkConnectionsFuture = scheduler.scheduleAtFixedRate(checkConnections, 0, TIMEOUT_TIME_MS, TimeUnit.MILLISECONDS);
        }
    }

    @OnMessage
    public void onMessage(Session session, AuctionEvent event, @PathParam("user") String user) {
        if (event.kind == AuctionEvent.Kind.NEW_BID) {
            if (event.currentPrice > currentHighestBid && sessions.containsKey(user)) {
                currentHighestBid = event.currentPrice;
                currentHighestBidder = user;

                // broadcast new bid event to all clients (even the sender, as confirmation)
                // create a new one because the username will be null in received events
                broadcast(AuctionEvent.createNewBidEvent(AuctionServer.objectName, currentHighestBid, currentHighestBidder));
            }
        }
    }

    @OnMessage
    public void onPong(PongMessage message, @PathParam("user") String user) {
        sessionPongTimes.put(user, System.currentTimeMillis());
    }

    @OnClose
    public void onClose(Session session, CloseReason reason, @PathParam("user") String user) {
        sessions.remove(user);

        broadcast(AuctionEvent.createClientLeftEvent(user));

        if (sessions.size() == 1) {
            // if this session closing means that only one session remains open, that one is the winner
            broadcast(AuctionEvent.createSoldEvent(AuctionServer.objectName, currentHighestBid, currentHighestBidder));

            System.out.format("'%s' was sold to '%s' for %f\n", AuctionServer.objectName, currentHighestBidder, currentHighestBid);

            try {
                sessions.get(currentHighestBidder).close();
            } catch (IOException ignored) {}

            scheduler.shutdownNow();
            AuctionServer.server.stop();
        }
    }

    private static void broadcast(AuctionEvent event) {
        sessions.forEach((user, session) -> {
            session.getAsyncRemote().sendObject(event);
        });
    }
}
