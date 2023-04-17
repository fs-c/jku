package chat.client;

import inout.In;
import inout.Out;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.SocketChannel;

import static chat.Globals.*;

public class ChatClient {
    private final String name;
    private final SocketChannel channel;
    private final ByteBuffer sendBuffer;
    private final ByteBuffer recvBuffer;
    private final Console console;
    private boolean terminate = false;
    private Thread receiverThread;

    private int sentMessages = 0;

    ChatClient(String name) throws IOException {
        this.name = name;
        channel = SocketChannel.open();
        sendBuffer = ByteBuffer.allocate(BUFFER_SIZE);
        recvBuffer = ByteBuffer.allocate(BUFFER_SIZE);
        console = new Console();
    }

    public static void main(String[] args) throws IOException {
        Out.println("=== Client starting ========");
        Out.print("Input client name: ");
        String name = In.readLine().trim();
        ChatClient client = new ChatClient(name);
        client.start();
    }

    public void start() {
        try {
            Out.println("---- Start -----------------");
            Out.println("---- Terminate with '.' ----");
            Out.println("---------- -----------------");

            // TODO: connect to server
            // TODO: Login with user name

            channel.connect(new InetSocketAddress(SERVER_IP, PORT));
            channel.configureBlocking(true);

            receiverThread = new Thread(() -> {
                while (!terminate) {
                    try {
                        var message = Message.deserialize(read(channel, recvBuffer));

                        if (message == null) {
                            Out.println("INTERNAL ERROR: couldn't deserialize incoming message");

                            return;
                        }

                        switch (message.kind) {
                            case CONNECTED -> {
                                write(channel, sendBuffer, Message.serialize(MsgKind.LOGIN, name));
                            }

                            case SEND -> {
                                if (!message.recipient.equals(name)) {
                                    Out.println("INTERNAL ERROR: this message was intended for a different recipient");
                                }

                                Out.println(String.format("Received from %s: %s", message.sender, message.content));

                                write(channel, sendBuffer, Message.serialize(MsgKind.ACKN, message.sender, name,
                                        String.valueOf(message.id)));
                            }

                            case TIMEOUT -> {
                                Out.println(String.format("Timeout: Message %d %s", message.id, message.sender));
                            }
                        }
                    } catch (Exception e) {
                        Out.println("Receiver interrupted");
                    }
                }
            });
            receiverThread.start();

            while (!terminate) {
                console.enter();
                String[] recMsgPair = console.readMessage();
                String receiver = recMsgPair[0];
                String content = recMsgPair[1];

                if (receiver.startsWith(".")) {
                    write(channel, sendBuffer, Message.serialize(MsgKind.LOGOUT, name));

                    terminate();
                } else {
                    int messageId = sentMessages++;

                    write(channel, sendBuffer, Message.serialize(MsgKind.SEND, name, receiver, String.valueOf(messageId), content));
                }
            }
        }
        //TODO: handle exception
        catch (Exception e) {
            Out.println("ERROR: " + e.getMessage());
        } finally {
            try {
                channel.close();
            } catch (IOException e) {
                Out.println("ERROR: " + e.getMessage());
            }
        }
    }

    private void terminate() {
        terminate = true;
        if (receiverThread != null) receiverThread.interrupt();

        try {
            channel.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Console allows synchronized input and print.
     * user can enter a synchronized  input mode which is then not
     * interrupted by print outputs.
     */
    private class Console {

        /**
         * Enter input mode
         */
        void enter() {
            String line = In.readLine();
        }

        /**
         * Read receiver and message without interruption from prints.
         *
         * @return the pair of receiver and message in an array
         */
        synchronized String[] readMessage() {
            Out.println("------------------------------");
            Out.print("Receiver: ");
            String receiver = In.readLine();
            Out.print("Message: ");
            String message = In.readLine();
            Out.println("------------------------------");
            return new String[]{receiver, message};
        }

        /**
         * Prints the message on the console.
         *
         * @param msg the message to print
         */
        synchronized void println(Object msg) {
            Out.println(msg);
        }

    }
}
