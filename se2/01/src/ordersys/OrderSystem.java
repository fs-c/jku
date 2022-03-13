package ordersys;

import java.lang.reflect.Array;
import java.util.Arrays;
import ordersys.Order;
import java.util.Iterator;
import java.util.function.Consumer;

record Item(int id, double price, String name) {
}

//class DynamicArray<T> implements Iterable<T> {
//    private T[] elements;
//    private int logicalLength = 0;
//
//    @SuppressWarnings("unchecked")
//    DynamicArray(Class<T> t, int initialSize) {
//        elements = (T[]) Array.newInstance(t, initialSize);
//    }
//
//    public T get(int index) {
//        if (index >= logicalLength) {
//            throw new ArrayIndexOutOfBoundsException();
//        }
//
//        return elements[index];
//    }
//
//    public void add(T element) {
//        if (logicalLength >= elements.length) {
//            elements = Arrays.copyOf(elements, logicalLength * 2);
//        }
//
//        elements[logicalLength++] = element;
//    }
//
//    public void delete(int index) {
//        if (index >= logicalLength) {
//            throw new ArrayIndexOutOfBoundsException();
//        }
//
//        // Indices are [ 0, 1, ..., index, index + 1, ..., logicalLength - 1 ]
//        // We move [ index + 1, ... logicalLength - 1 ] to the left by one, thus
//        // overwriting the element at index
//        System.arraycopy(elements, index + 1, elements, index, logicalLength - 1 - index);
//
//        logicalLength--;
//    }
//
//    @Override
//    public Iterator<T> iterator() {
//        return new DynamicArrayIterator();
//    }
//
//    class DynamicArrayIterator implements Iterator<T> {
//        private int index = 0;
//
//        @Override
//        public boolean hasNext() {
//            return index <= logicalLength;
//        }
//
//        @Override
//        public T next() {
//            return get(index++);
//        }
//
//        @Override
//        public void remove() {
//            delete(index);
//        }
//    }
//}

//class DynamicArray<T> {
//    private T[] elements;
//    private int logicalLength = 0;
//
//    @SuppressWarnings("unchecked")
//    DynamicArray(Class<T> t, int initialSize) {
//        elements = (T[]) Array.newInstance(t, initialSize);
//    }
//
//    public int size() {
//        return logicalLength;
//    }
//
//    public void add(T element) {
//        if (logicalLength >= elements.length) {
//            elements = Arrays.copyOf(elements, logicalLength * 2);
//        }
//
//        elements[logicalLength++] = (T) element;
//    }
//
//    public T get(int index) {
//        if (index >= logicalLength) {
//            throw new ArrayIndexOutOfBoundsException();
//        }
//
//        return (T) elements[index];
//    }
//
//    public void remove(int index) {
//        if (index >= logicalLength) {
//            throw new ArrayIndexOutOfBoundsException();
//        }
//
//        // Indices are [ 0, 1, ..., index, index + 1, ..., logicalLength - 1 ]
//        // We move [ index + 1, ... logicalLength - 1 ] to the left by one, thus
//        // overwriting the element at index
//        System.arraycopy(elements, index + 1, elements, index, logicalLength - 1 - index);
//
//        logicalLength--;
//    }
//}

public class ItemList {
    public void add(Item item) {

    }

    public void removeById(int itemId) {

    }

    public Item getById(int itemId) {

    }

    private int getIndexById(int itemId) {

    }
}

public class OrderList {
    private Order[] orders = new Order[2];

    public void add(Order order) {

    }

    public Order getById(int orderId) {

    }
}

public class OrderSystem {
    private static int runningItemId = 0;
    private static int runningOrderId = 0;

    private final ItemList items = new ItemList();
    private final OrderList orders = new OrderList();

    public int addItem(double price, String name) {
        Item item = new Item(runningItemId++, price, name);

        items.add(item);

        return item.id();
    }

    public void removeItem(int id) {
        items.removeById(id);
    }

    public int addOrder(int itemId, int quantity) {
        Item item = items.getById(itemId);
        Order order = new Order(runningOrderId++, item, quantity, Order.Status.OPEN);

        orders.add(order);

        return order.getId();
    }

    public void setOrderStatus(int orderId, Order.Status status) {
        orders.getById(orderId).setStatus(status);
    }

    public Order[] getAllOrders() {

    }

    public Order[] getOrdersByStatus(Order.Status status) {

    }

    public Order[] getOpenOrders() {

    }

    public Order[] getOrdersByItem(int itemId) {

    }
}
