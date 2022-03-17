package transport;

public record Cargo(Cargo.Type type, String name, int weight) {
    enum Type {
        SOLID, LIQUID
    }
}
