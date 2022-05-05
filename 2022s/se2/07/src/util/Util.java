package util;

import java.util.Collection;
import java.util.List;
import java.util.ArrayList;
import java.util.Optional;
import java.util.function.Predicate;

public class Util {
    /**
     * Filters a collection by the given predicate
     * @param coll the collection
     * @param pred the predicate
     * @param <E> the element type
     * @return a list of filtered elements
     */
    public static <E> List<E> filter(Collection<E> coll, Predicate<? super E> pred) {
        List<E> filtered = new ArrayList<>();
        for (E e: coll) {
            if (pred.test(e)) {
                filtered.add(e);
            }
        }
        return filtered;
    }

    /**
     * Finds an element in the given collections which fulfills the given predicate
     * @param coll the collection
     * @param pred the predicate
     * @param <E> the element type
     * @return element in an Optional if found, Optional.empty() otherwise
     */
    public static <E> Optional<E> find(Collection<E> coll, Predicate<? super E> pred) {
        for (E e: coll) {
            if (pred.test(e)) {
                return Optional.of(e);
            }
        }
        return Optional.empty();
    }

    /**
     * Tests if there is an element in the given collection fulfilling the given predicate
     * @param coll the collection
     * @param pred the predicate
     * @param <E> the element type
     * @return true if an element found, false otherwise
     */
    public static <E> boolean exists(Collection<E> coll, Predicate<? super E> pred) {
        return find(coll, pred).isPresent();
    }

    /**
     * Tests if there is no element in the given collection fulfilling the given predicate
     * @param coll the collection
     * @param pred the predicate
     * @param <E> the element type
     * @return true if no element found, false otherwise
     */
    public static <E> boolean notExists(Collection<E> coll, Predicate<? super E> pred) {
        return find(coll, pred).isEmpty();
    }

    /**
     * Tests if all elements in the given collection fulfill the given predicate
     * @param coll the collection
     * @param pred the predicate
     * @param <E> the element type
     * @return true if all elements fulfill the predicate, false otherwise
     */
    public static <E> boolean all(Collection<E> coll, Predicate<? super E> pred) {
        return find(coll, pred.negate()).isEmpty();
    }

}
