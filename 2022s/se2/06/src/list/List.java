package list;

public interface List<E> extends Iterable<E> {

	/**
	 * Returns the number of elements of this list
	 * @return the number of elements
	 */
	int size();

	/**
	 * Adds an element to this list
	 * @param elem the element to be added
	 */
	void add(E elem);

	/** Tests if the object is contained in this list
	 * @param obj the object to be tested
	 * @return true if obj is contained, false otherwise
	 */
	boolean contains(Object obj);

	/**
	 * Adds all elements of the specified Iterable to this list
	 * @param elems the Iterable elements to be added
	 */
	void addAll(Iterable<? extends E> elems);

	/**
	 * Tests if all objects of the specified Iterable are contained in this list
	 * @param c the Iterable objects to be tested
	 * @return true if all objects of c are contained, false otherwise
	 */
	boolean containsAll(Iterable<?> c);

	static <X> List<X> of(X... values) {
		LinkedList<X> l = new LinkedList<X>();
		for(X val : values) {
			l.add(val);
		}
		return l;
	}
}
