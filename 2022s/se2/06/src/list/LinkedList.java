package list;

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * This linked list implementation shows the use of generics and inner classes
 *
 * @param <E> the element type
 */
public class LinkedList<E> implements List<E> {

    @Override
    public int size() {
        return n;
    }

    public void add(E elem) {
        head = new Node<E>(elem, head);
        n++;
    }

    @Override
    public boolean contains(Object obj) {
        for (E elem : this) {
            if (elem.equals(obj))
                return true;
        }
        return false;
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<E>() {

            private Node<E> current = head;

            @Override
            public boolean hasNext() {
                return current != null;
            }

            @Override
            public E next() {
                if (current != null) {
                    E value = current.value;
                    current = current.next;
                    return value;
                } else {
                    throw new NoSuchElementException("No more element in list");
                }
            }

        };
    }

    // private and protected --------------------------------------------------

    protected Node<E> head = null;

    protected int n = 0;

    // inner class Node -------------------------------------------------------

    protected static class Node<F> {
        final F value;
        Node<F> next;

        Node(F elem, Node<F> next) {
            this.value = elem;
            this.next = next;
        }
    }

    // additional methods -----------------------------------------------------

    @Override
    public void addAll(Iterable<? extends E> elems) {
        for (E e : elems) {
            add(e);
        }
    }

    @Override
    public boolean containsAll(Iterable<?> elems) {
        for (Object e : elems) {
            if (!contains(e))
                return false;
        }
        return true;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("[");
        int i = 0;
        for (E e : this) {
            i++;
            sb.append(e);
            if (i != n) {
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }
}
