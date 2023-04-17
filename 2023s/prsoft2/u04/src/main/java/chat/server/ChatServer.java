package chat.server;

import inout.In;
import inout.Out;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;
import java.nio.channels.ServerSocketChannel;
import java.nio.channels.SocketChannel;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

import static chat.Globals.*;

public class ChatServer {
    private final ServerSocketChannel server;
    private final ByteBuffer buffer;
    private final Selector selector;
    private final Thread selectorThread;
    private final Map<String, SocketChannel> clients = new HashMap<>();
    private final ScheduledExecutorService timeoutScheduler = Executors.newScheduledThreadPool(1);
    private final Map<String, Future<?>> pendingTimeouts = new HashMap<>();
    private volatile boolean terminate = false;

    ChatServer() throws IOException {
        server = ServerSocketChannel.open();
        selector = Selector.open();
        selectorThread = new Thread(new SelectorRunnable());
        buffer = ByteBuffer.allocate(BUFFER_SIZE);

        server.configureBlocking(false);
    }

    public static void main(String[] args) throws IOException {
        ChatServer server = new ChatServer();
        server.start();
    }

    public void start() {
        Out.println("=== Server starting at port %d ========".formatted(PORT));
        try {
            server.socket().bind(new InetSocketAddress(PORT));

            server.register(selector, SelectionKey.OP_ACCEPT);

            selectorThread.start();

            Out.println("=== Server started ========");
            Out.println("Terminate with enter ... ");
            In.readLine();
            terminate();

            selectorThread.join();

        }
        //TODO: handle IOException
        catch (Exception e) {
            Out.println("ERROR: " + e.getMessage());
        }
    }

    public void terminate() {
        terminate = true;
        selectorThread.interrupt();
    }

    private class SelectorRunnable implements Runnable {
        public void handleReceivedMessage(SocketChannel channel, String serializedMessage) throws IOException {
            var message = Message.deserialize(serializedMessage);

            if (message == null) {
                Out.println("INTERNAL ERROR: %s couldn't be deserialized".formatted(serializedMessage));

                return;
            }

            switch (message.kind) {
                case LOGIN -> {
                    if (clients.containsKey(message.sender)) {
                        write(channel, buffer, Message.serialize(MsgKind.FAILED_LOGIN, "duplicate name"));
                    } else {
                        clients.put(message.sender, channel);

                        write(channel, buffer, Message.serialize(MsgKind.OK_LOGIN, message.sender));
                    }
                }

                case LOGOUT -> {
                    write(channel, buffer, Message.serialize(MsgKind.OK_LOGOUT, message.sender));

                    clients.remove(message.sender);
                    channel.close();
                }

                case SEND -> {
                    var recipientChannel = clients.get(message.recipient);

                    if (recipientChannel == null) {
                        write(channel, buffer, Message.serialize(MsgKind.FAILED_SEND, "recipient not logged in"));
                    } else {
                        write(recipientChannel, buffer, Message.serialize(MsgKind.SEND, message.sender, message.recipient,
                                String.valueOf(message.id), message.content));

                        // todo: some kind of proper composite key mechanism would be good
                        var timeoutKey = message.recipient + NAME_SEP + message.id;
                        pendingTimeouts.put(timeoutKey, timeoutScheduler.schedule(() -> {
                            try {
                                write(channel, buffer, Message.serialize(MsgKind.TIMEOUT, message.sender, message.recipient,
                                        String.valueOf(message.id)));
                            } catch (IOException e) {
                                e.printStackTrace();
                            }
                        }, TIMEOUT_MS, TimeUnit.MILLISECONDS));
                    }
                }

                case ACKN -> {
                    var recipientChannel = clients.get(message.recipient);

                    if (recipientChannel != null) {
                        write(recipientChannel, buffer, Message.serialize(MsgKind.ACKN, message.recipient, message.sender,
                                String.valueOf(message.id)));
                    }

                    var timeoutKey = message.sender + NAME_SEP + message.id;
                    var pendingTimeout = pendingTimeouts.get(timeoutKey);

                    if (pendingTimeout != null) {
                        pendingTimeout.cancel(true);
                    }
                }
            }
        }

        public void run() {
            while (!terminate) {
                try {
                    selector.select();

                    var keyIterator = selector.selectedKeys().iterator();
                    while (keyIterator.hasNext()) {
                        var key = keyIterator.next();

                        if (key.isAcceptable()) {
                            var channel = server.accept();
                            channel.configureBlocking(false);
                            channel.register(selector, SelectionKey.OP_READ);

                            write(channel, buffer, Message.serialize(MsgKind.CONNECTED));
                        } else if (key.isReadable()) {
                            try {
                                var channel = (SocketChannel) key.channel();
                                var message = read(channel, buffer);

                                handleReceivedMessage(channel, message);
                            } catch (IOException e) {
                                Out.println("ERROR: client failed " + e.getMessage());
                            }
                        } else {
                            Out.println("ERROR: unknown event " + key);
                        }

                        keyIterator.remove();
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
    }

}
