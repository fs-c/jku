package map;

import java.util.Iterator;

public class SimpleMap<K, V>  implements Map<K, V> {
    record Entry<K, V>(K key, V value) implements KeyValuePair<K, V> {
        @Override
        public K getKey() {
            return key;
        }

        @Override
        public V getValue() {
            return value;
        }
    }

    protected LinkedList<Entry<K, V>> list = new LinkedList<>();

    @Override
    public void put(K key, V value) {
        list.add(new Entry<>(key, value));
    }

    @Override
    public V get(Object key) {
        list.reset();

        while (!list.atEnd()) {
            Entry<K, V> entry = list.next();

            if (entry.getKey() == key) {
                return entry.getValue();
            }
        }

        return null;
    }

    @Override
    public boolean contains(Object key) {
        return get(key) != null;
    }

    @Override
    public boolean remove(Object key) {
        list.reset();

        while (!list.atEnd()) {
            Entry<K, V> entry = list.current();

            if (entry.getKey() == key) {
                list.remove();

                return true;
            }

            list.advance();
        }

        return false;
    }

    @Override
    public int size() {
        return list.getSize();
    }

    @Override
    public Iterator<K> keyIterator() {
        list.reset();

        return new Iterator<>() {
            @Override
            public boolean hasNext() {
                return !list.atEnd();
            }

            @Override
            public K next() {
                return list.next().getKey();
            }
        };
    }

    @Override
    public Iterator<V> valueIterator() {
        list.reset();

        return new Iterator<>() {
            @Override
            public boolean hasNext() {
                return !list.atEnd();
            }

            @Override
            public V next() {
                return list.next().getValue();
            }
        };
    }

    @Override
    public Iterator<KeyValuePair<K, V>> iterator() {
        list.reset();

        return new Iterator<>() {
            @Override
            public boolean hasNext() {
                return !list.atEnd();
            }

            @Override
            public Entry<K, V> next() {
                return list.next();
            }
        };
    }
}
