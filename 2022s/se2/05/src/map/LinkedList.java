package map;

class LinkedList<E> {
    private static class Node<E> {
        final E element;
        Node<E> next;

        public Node(E element, Node<E> next) {
            this.element = element;
            this.next = next;
        }
    }

    private Node<E> head;
    private Node<E> cur;

    private int size = 0;

    LinkedList() {
        // First node is a dummy element to simplify implementation
        head = cur = new Node<E>(null, null);
    }

    public int getSize() {
        return size;
    }

    public boolean atEnd() {
        return cur.next == null;
    }

    public E current() {
        return cur.next.element;
    }

    public void advance() {
        cur = cur.next;
    }

    public E next() {
        E element = current();

        advance();

        return element;
    }

    public void add(E element) {
        size++;

        cur.next = new Node<E>(element, cur.next);
    }

    public void remove() {
        size--;

        cur.next = cur.next.next;
    }

    public void reset() {
        cur = head;
    }
}
