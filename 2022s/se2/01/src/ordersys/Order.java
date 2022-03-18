package ordersys;

import java.util.Objects;

public class Order {
    public enum Status {
        OPEN, PROCESSING, FULFILLED, CANCELLED
    }

    private final Item item;
    private final int quantity;
    private final double totalCost;

    private Status status;

    Order(Item item, int quantity, Status status) {
        this.item = item;
        this.quantity = quantity;
        this.totalCost = item.price() * quantity;
        this.status = status;
    }

    public Item getItem() {
        return item;
    }

    public int getQuantity() {
        return quantity;
    }

    public double getTotalCost() {
        return totalCost;
    }

    public Status getStatus() {
        return status;
    }

    public String toString() {
        return String.format("Order{ item: '%s', quantity: %d, total %f, status: %s }",
                item.name(), quantity, totalCost, status);
    }

    protected void setStatus(Status status) {
        this.status = status;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Order order = (Order) o;
        return quantity == order.quantity && Double.compare(order.totalCost, totalCost) == 0 && item.equals(order.item) && status == order.status;
    }

    @Override
    public int hashCode() {
        return Objects.hash(item, quantity, totalCost, status);
    }
}

