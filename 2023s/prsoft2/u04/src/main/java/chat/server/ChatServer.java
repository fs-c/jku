package chat.server;

import chat.Globals;
import inout.In;
import inout.Out;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.*;
import java.util.HashMap;
import java.util.Map;

import static chat.Globals.*;

public class ChatServer {
    private final ServerSocketChannel server;
    private final ByteBuffer buffer;
    private final Selector selector;
    private final Thread selectorThread;
    private volatile boolean terminate = false;

    private Map<String, SocketChannel> clients = new HashMap<>();

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
        public void handleReceivedMessage(SocketChannel channel, String message) throws IOException {
            if (message.startsWith(MsgKind.LOGIN.name())) {
                var name = message.split(":")[1];

                if (name.length() == 0) {
                    write(channel, buffer, MsgKind.FAILED_LOGIN + MSG_SEP + "invalid format");
                } else if (clients.containsKey(name)) {
                    write(channel, buffer, MsgKind.FAILED_LOGIN + MSG_SEP + "duplicate name");
                } else {
                    clients.put(name, channel);

                    write(channel, buffer, MsgKind.OK_LOGIN.name());
                }
            } else if (message.startsWith(MsgKind.SEND.name())) {
                var chunks = message.split(";");

                if (chunks.length == 0) {
                    write(channel, buffer, Message.serialize());
                    return;
                }

                var sender = chunks[0].split(":")[1];
                var recipient = chunks[1];
                var recipientChannel = clients.get(chunks[1]);
                var id = chunks[2];
                var content = chunks[3];

                if (sender.length() == 0 || content.length() == 0 || recipient.length() == 0) {
                    write(channel, buffer, MsgKind.FAILED_SEND + MSG_SEP + "invalid format");
                } else if (recipientChannel == null) {
                    write(channel, buffer, MsgKind.FAILED_SEND + MSG_SEP + "recipient not logged in");
                } else {
                    write(recipientChannel, buffer, MsgKind.SEND + ":" + sender + MSG_SEP + recipient + MSG_SEP + id + MSG_SEP + content);
                }
            } else if (message.startsWith(MsgKind.LOGOUT.name())) {
                var name = message.split(":")[1];

                channel.close();
                clients.remove(name);

                write(channel, buffer, MsgKind.OK_LOGOUT.name());
            } else if (message.startsWith(MsgKind.ACKN.name())) {
                var name = message.split(";")[0].split(":")[1];
                var recipientChannel = clients.get(name);

                write(recipientChannel, buffer, message);
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

                            write(channel, buffer, MsgKind.CONNECTED.name());
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
