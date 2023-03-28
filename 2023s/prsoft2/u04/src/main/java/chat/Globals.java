package chat;

import inout.Out;

import java.io.IOException;
import java.io.Serializable;
import java.nio.ByteBuffer;
import java.nio.channels.SocketChannel;
import java.nio.charset.Charset;

public class Globals {
    public static final int PORT = 6789;
    public static final String SERVER_IP = "localhost";
    public static final int BUFFER_SIZE = 128;
    public static final String MSG_SEP = ";";
    public static final String NAME_SEP = ":";
    public static Charset CSET = Charset.forName("UTF-8");

    public static String read(SocketChannel channel, ByteBuffer buffer) throws IOException {
        buffer.clear();
        int n = channel.read(buffer);
        buffer.flip();

        String msg = CSET.decode(buffer).toString();
        Out.println("  <- IN  <- '%s' (%d)".formatted(msg, n));

        return msg;
    }

    public static int write(SocketChannel channel, ByteBuffer buffer, String msg) throws IOException {
        buffer.clear();
        buffer.put(CSET.encode(msg));
        buffer.flip();

        int written = channel.write(buffer);
        Out.println("  -> OUT -> '%s'".formatted(msg));

        return written;
    }

    public enum MsgKind {
        CONNECTED, LOGIN, OK_LOGIN, FAILED_LOGIN, LOGOUT, OK_LOGOUT, SEND, ACKN, FAILED_SEND, TIMEOUT
    }

    public static class Message {
        public static String serialize(MsgKind kind, String ...content) {
            var serialized = new StringBuilder();

            serialized.append(kind);

            for (var c : content) {
                serialized.append(MSG_SEP).append(c);
            }

            return serialized.toString();
        }

        public static Message deserialize(String serializedMessage) {
            var deserialized = new Message();
            var chunks = serializedMessage.split(MSG_SEP);

            deserialized.kind = MsgKind.valueOf(chunks[0]);

            switch (deserialized.kind) {
                case CONNECTED -> {
                    if (chunks.length != 1) {
                        throw new RuntimeException("invalid format");
                    }
                }
                case LOGIN, OK_LOGIN, LOGOUT, OK_LOGOUT -> {
                    if (chunks.length != 2) {
                        throw new RuntimeException("invalid format");
                    }

                    deserialized.sender = chunks[1];
                }
                case FAILED_LOGIN, FAILED_SEND -> {
                    if (chunks.length != 2) {
                        throw new RuntimeException("invalid format");
                    }

                    deserialized.content = chunks[1];
                }
                case SEND -> {
                    if (chunks.length != 5) {
                        throw new RuntimeException("invalid format");
                    }

                    deserialized.sender = chunks[1];
                    deserialized.recipient = chunks[2];
                    deserialized.content = chunks[3];
                    deserialized.id = Integer.parseInt(chunks[4]);
                }
                case ACKN -> {
                    if (chunks.length != 4) {
                        throw new RuntimeException("invalid format");
                    }

                    deserialized.sender = chunks[1];
                    deserialized.recipient = chunks[2];
                    deserialized.id = Integer.parseInt(chunks[3]);
                }
            }

            return deserialized;
        }

        public MsgKind kind;
        public String sender;
        public String recipient;
        public String content;
        public int id;
    }

    public static String serializeConnected() {
        return MsgKind.CONNECTED.name();
    }

    public static String serialializeLogin(String name) {
        return MsgKind.LOGIN.name() + NAME_SEP + name;
    }

    public static String serializeOkLogin(String name) {
        return MsgKind.OK_LOGIN.name() + NAME_SEP + name;
    }

    public static String serializeFailedLogin(String reason) {
        return MsgKind.FAILED_LOGIN.name() + MSG_SEP + reason;
    }

    public static String serializeLogout(String name) {
        return MsgKind.LOGOUT.name() + NAME_SEP + name;
    }

    public static String serializeOkLogout() {
        return MsgKind.OK_LOGOUT.name();
    }

    public static String serializeSend(String sender, String recipient, String content, int id) {
        return "";
    }

    public static String serializeAckn(String sender, String recipient, int id) {
        return "";
    }

    public static String serializeFailedSend(String reason) {
        return "";
    }

    public static String serializeTimeout(String sender, String recipient, int id) {
        return "";
    }
}
