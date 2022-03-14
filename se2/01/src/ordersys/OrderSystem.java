package ordersys;

import java.util.Arrays;
import java.lang.reflect.Array;

class NotFoundException extends RuntimeException {
}

class DynamicArray<T> {
    private T[] elements;
    private int logicalLength = 0;

    @SuppressWarnings("unchecked")
    DynamicArray(Class<T> t, int initialSize) {
        elements = (T[]) Array.newInstance(t, initialSize);
    }

    public int size() {
        return logicalLength;
    }

    public int add(T element) {
        if (logicalLength >= elements.length) {
            elements = Arrays.copyOf(elements, logicalLength * 2);
        }

        elements[logicalLength] = element;

        return logicalLength++;
    }

    public T get(int index) {
        if (index >= logicalLength) {
            throw new NotFoundException();
        }

        return elements[index];
    }

    public void remove(int index) {
        if (index >= logicalLength) {
            throw new NotFoundException();
        }

        // Indices are [ 0, 1, ..., index, index + 1, ..., logicalLength - 1 ]
        // We move [ index + 1, ... logicalLength - 1 ] to the left by one, thus
        // overwriting the element at index
        System.arraycopy(elements, index + 1, elements, index, logicalLength - 1 - index);

        logicalLength--;
    }
}

class ItemList extends DynamicArray<Item> {
    ItemList() {
        super(Item.class, 2);
    }

    public void removeById(int itemId) {
        remove(getIndexById((itemId)));
    }

    public Item getById(int itemId) {
        return get(getIndexById(itemId));
    }

    private int getIndexById(int itemId) {
        for (int i = 0; i < size(); i++) {
            if (get(i).id() == itemId) {
                return i;
            }
        }

        throw new NotFoundException();
    }
}

class OrderList extends DynamicArray<Order> {
    OrderList() {
        super(Order.class, 2);
    }
}

public class OrderSystem {
    private static int runningItemId = 0;

    private final ItemList items = new ItemList();
    private final OrderList orders = new OrderList();

    public int addItem(Item item) {
        if (item == null) {
            return -1;
        }

        items.add(item);

        return item.id();
    }

    public int addItem(double price, String name) {
        Item item = new Item(runningItemId++, price, name);

        items.add(item);

        return item.id();
    }

    public boolean removeItem(int id) {
        try {
            items.removeById(id);

            return true;
        } catch (NotFoundException err) {
            return false;
        }
    }

    public int addOrder(int itemId, int quantity) {
        if (quantity < 1) {
            return -1;
        }

        try {
            Item item = items.getById(itemId);
            Order order = new Order(item, quantity, Order.Status.OPEN);

            return orders.add(order);
        } catch (NotFoundException err) {
            return -1;
        }
    }

    public boolean setOrderStatus(int orderIndex, Order.Status status) {
        try {
            orders.get(orderIndex).setStatus(status);

            return true;
        } catch (NotFoundException err) {
            return false;
        }
    }

    public Order[] getAllOrders() {
        Order[] result = new Order[orders.size()];

        for (int i = 0; i < orders.size(); i++) {
            result[i] = orders.get(i);
        }

        return result;
    }

    public Order[] getOrdersByStatus(Order.Status status) {
        Order[] temp = new Order[orders.size()];

        int j = 0;
        for (int i = 0; i < orders.size(); i++) {
            if (orders.get(i).getStatus() == status) {
                temp[j++] = orders.get(i);
            }
        }

        Order[] result = new Order[j];
        System.arraycopy(temp, 0, result, 0, j);

        return result;
    }

    public Order[] getOpenOrders() {
        Order[] open = getOrdersByStatus(Order.Status.OPEN);
        Order[] processing = getOrdersByStatus(Order.Status.PROCESSING);

        Order[] result = new Order[open.length + processing.length];

        System.arraycopy(open, 0, result, 0, open.length);
        System.arraycopy(processing, 0, result, open.length, processing.length);

        return result;
    }

    public Order[] getOrdersByItem(int itemId) {
        Order[] temp = new Order[orders.size()];

        int j = 0;
        for (int i = 0; i < orders.size(); i++) {
            if (orders.get(i).getItem().id() == itemId) {
                temp[j++] = orders.get(i);
            }
        }

        Order[] result = new Order[j];
        System.arraycopy(temp, 0, result, 0, j);

        return result;
    }
}
