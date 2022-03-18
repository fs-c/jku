package transport;

public record Cargo(Cargo.Type type, String name, int weight) {
    public enum Type {
        SOLID, LIQUID
    }
}
