package map;

import list.LinkedList;
import list.List;

import java.util.Iterator;
import java.util.Optional;
import java.util.function.*;

public class SimpleMap<K, V> implements Map<K, V> {
    protected static class Node<D> {
        protected Node<D> next;
        protected D data;

        protected Node(Node<D> next, D data) {
            this.next = next;
            this.data = data;
        }
    }

    public static class Entry<K, V> implements KeyValuePair<K, V> {
        private final K key;
        private V value;

        Entry(K key, V value) {
            this.key = key;
            this.value = value;
        }

        @Override
        public K getKey() {
            return key;
        }

        @Override
        public V getValue() {
            return value;
        }

        @Override
        public String toString() {
            return "Entry{" +
                    "key=" + key +
                    ", value=" + value +
                    '}';
        }
    }

    private abstract class AbstractMapIterator<X> implements Iterator<X> {
        protected Node<Entry<K, V>> cur = head;

        @Override
        public boolean hasNext() {
            return cur != null;
        }

        protected void moveToNext() {
            cur = cur.next;
        }
    }

    private class KeyIterator extends AbstractMapIterator<K> {
        @Override
        public K next() {
            K toReturn = cur.data.key;
            moveToNext();
            return toReturn;
        }
    }

    private class ValueIterator extends AbstractMapIterator<V> {
        @Override
        public V next() {
            V toReturn = cur.data.value;
            moveToNext();
            return toReturn;
        }
    }

    private class EntryIterator extends AbstractMapIterator<KeyValuePair<K, V>> {
        @Override
        public Entry<K, V> next() {
            Entry<K, V> toReturn = cur.data;
            moveToNext();
            return toReturn;
        }
    }

    protected Node<Entry<K, V>> head = null;
    protected int size = 0;

    @Override
    public boolean putIfAbsent(K k, Supplier<? extends V> valueSupplier) {
        if (contains(k)) {
            return false;
        }

        put(k, valueSupplier.get());

        return true;
    }

    public Map<K, V> filter(BiPredicate<? super K, ? super V> predicate) {
        Map<K, V> filtered = new SimpleMap<>();

        for (KeyValuePair<K, V> pair : this) {
            if (predicate.test(pair.getKey(), pair.getValue())) {
                filtered.put(pair.getKey(), pair.getValue());
            }
        }

        return filtered;
    }

    @Override
    public <NV> Map<K, NV> mapValues(BiFunction<? super K, ? super V, ? extends NV> newValueGenerator) {
        Map<K, NV> newMap = new SimpleMap<>();

        for (KeyValuePair<K, V> pair : this) {
            newMap.put(pair.getKey(), newValueGenerator.apply(pair.getKey(), pair.getValue()));
        }

        return newMap;
    }

    @Override
    public Optional<KeyValuePair<K, V>> find(Predicate<? super KeyValuePair<K, V>> predicate) {
        for (KeyValuePair<K, V> pair : this) {
            if (predicate.test(pair)) {
                return Optional.of(pair);
            }
        }

        return Optional.empty();
    }

    @Override
    public boolean none(Predicate<? super KeyValuePair<K, V>> predicate) {
        return !some(predicate);
    }

    @Override
    public boolean all(Predicate<? super KeyValuePair<K, V>> predicate) {
        return !some(predicate.negate());
    }

    @Override
    public boolean some(Predicate<? super KeyValuePair<K, V>> predicate) {
        return find(predicate).isPresent();
    }

    @Override
    public void put(K key, V value) {
        Node<Entry<K, V>> cur = head;
        while (cur != null && !cur.data.key.equals(key)) {
            cur = cur.next;
        }
        if (cur != null) {
            cur.data.value = value;
        } else {
            head = new Node<>(head, new Entry<>(key, value));
			size++;
        }
    }

    @Override
    public V get(Object key) {
        Node<Entry<K, V>> cur = head;
        while (cur != null && !cur.data.key.equals(key)) {
            cur = cur.next;
        }
        if (cur != null) {
            return cur.data.value;
        }
        return null;
    }

    @Override
    public boolean contains(Object key) {
        return get(key) != null;
    }

    @Override
    public boolean remove(Object key) {
        Node<Entry<K, V>> prev = null;
        Node<Entry<K, V>> cur = head;
        while (cur != null && !cur.data.key.equals(key)) {
            prev = cur;
            cur = cur.next;
        }
        if (cur != null) {
            if (cur == head) {
                head = cur.next;
            } else {
                prev.next = cur.next;
            }
            size--;
            return true;
        }
        return false;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public KeyIterator keyIterator() {
        return new KeyIterator();
    }

    @Override
    public ValueIterator valueIterator() {
        return new ValueIterator();
    }

    @Override
    public EntryIterator iterator() {
        return new EntryIterator();
    }
}
