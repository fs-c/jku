class DictionaryTest {
    public static void main(String[] args) {

    }
}

class Dictionary {
    private Entry head = null; 

    void insert(String term, String translation) {
        Entry cur = head, prev = null;
        Entry e = new Entry(term, translation);

        while (cur != null && term.compareTo(cur.term) > 0) {
            prev = cur;
            cur = cur.next;
        }

        if (cur != null && cur.term == term)
            return;

        if (prev == null) {
            head = e;
        } else prev.next = e;

        e.next = cur;
    }

    void delete(String term) {
        Entry cur = head, prev = null;

        while (cur != null && !term.equals(cur.term)) {
            prev = cur;
            cur = cur.next;
        }

        if (cur == null)
            return;

        prev.next = cur.next;
    }

    String lookup(String term) {
        Entry cur = head;

        while (cur != null && !term.equals(cur.term)) {
            cur = cur.next;
        }
        
        return (cur ? cur.term : null);
    }

    @Override
    public String toString() {
        Entry cur = head;
        StringBuilder builder = new StringBuilder();

        while (cur != null) {
            builder.append(cur.toString() + '\n');

            cur = cur.next;
        }

        return builder.toString();
    }
    
    private static class Entry {
        String term;
        String translation;
        
        Entry next = null;

        Entry(String term, String translation) {
            this.term = term;
            this.translation = translation;
        }

        @Override
        public String toString() {
            return this.term + " - " + this.translation;
        }
    } 
}
