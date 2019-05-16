class Dictionary {
    public static void main(String[] args) {
        final var dict = new Dictionary();

        dict.insert("better", "besser");
        Out.println(dict.toString());

        dict.insert("apple", "Apfel");
        Out.println(dict.toString());

        dict.insert("deft", "geschickt");
        Out.println(dict.toString());

        dict.insert("control", "Kontrolle");
        Out.println(dict.toString());

        Out.format("Lookup 'better': %s%n", dict.lookup("better"));
    }

    private Entry head = null; 

    void insert(String term, String translation) {
        Entry cur = head, prev = null;
        final var e = new Entry(term, translation);

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
        
        return (cur != null ? cur.translation : null);
    }

    @Override
    public String toString() {
        Entry cur = head;
        final var builder = new StringBuilder();

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
