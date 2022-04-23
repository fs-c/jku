package map;

import inout.Out;

public class SortedMap<K extends Comparable<K>, V> extends SimpleMap<K, V> {
    @Override
    public void put(K key, V value) {
        if (size() == 0) {
            super.put(key, value);

            return;
        }

        list.reset();

        while (!list.atEnd()) {
            if (list.current().getKey().compareTo(key) > 0) {
                super.put(key, value);

                return;
            }

            list.advance();
        }

        super.put(key, value);
    }
}
