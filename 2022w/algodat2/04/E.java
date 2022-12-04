import java.util.Objects;

public class E {
    public final V first;
    public final V second;
    public final int weight;

    public E(V first, V second, int weight) {
        this.first = first;
        this.second = second;
        this.weight = weight;
    }

    @Override
    public String toString() {
        return "(" + first + " <- " + weight + " -> " + second + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        E e = (E) o;
        return weight == e.weight && Objects.equals(first, e.first) && Objects.equals(second, e.second);
    }

    @Override
    public int hashCode() {
        return Objects.hash(first, second, weight);
    }
}
