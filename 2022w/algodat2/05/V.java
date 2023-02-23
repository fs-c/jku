import java.util.Objects;

public class V {
    public final int idx;
    public final String name;

    public V(int idx, String name) {
        this.idx = idx;
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        V v = (V) o;
        return Objects.equals(name, v.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }
}
