package ordersys.app;

import inout.Out;

import ordersys.Item;
import ordersys.Order;
import ordersys.OrderSystem;

public class OrderApp {
    public static void main(String[] args) {
        OrderSystem system = new OrderSystem();

        Item screw = new Item(0, 2.5, "100pcs M2 8mm Screws");
        Item screwdriver = new Item(1, 7, "Simple Screwdriver");
        Item nail = new Item(2, 2, "20pcs 40mm Nails");
        Item hammer = new Item(3, 15, "Simple Hammer");

        int screwItemId = system.addItem(screw);
        int screwdriverItemId = system.addItem(screwdriver);
        int nailItemId = system.addItem(nail);
        int hammerItemId = system.addItem(hammer);

        int screwsOrderId = system.addOrder(screwItemId, 10);
        int screwdriverOrderId = system.addOrder(screwdriverItemId, 2);
        int firstNailsOrderId = system.addOrder(nailItemId, 11);
        int secondNailsOrderId = system.addOrder(nailItemId, 1);
        int hammerOrderId = system.addOrder(hammerItemId, 1);

        Out.println("PRINTING ORDERS AFTER PART 1:");

        printOrders(system.getAllOrders());

        system.setOrderStatus(screwsOrderId, Order.Status.CANCELLED);

        int newScrewsOrderId = system.addOrder(screwItemId, 1);

        system.setOrderStatus(screwdriverOrderId, Order.Status.PROCESSING);
        system.setOrderStatus(firstNailsOrderId, Order.Status.FULFILLED);
        system.setOrderStatus(secondNailsOrderId, Order.Status.PROCESSING);
        system.setOrderStatus(hammerOrderId, Order.Status.FULFILLED);

        Out.println("PRINTING ORDERS AFTER PART 2:");

        printOrders(system.getAllOrders());

        Out.println("PRINTING ALL FULFILLED ORDERS:");

        printOrders(system.getOrdersByStatus(Order.Status.FULFILLED));

        Out.println("PRINTING ALL ORDERS OF NAILS:");

        printOrders(system.getOrdersByItem(nailItemId));

        Out.println("PRINTING ALL OPEN ORDERS");

        printOrders(system.getOpenOrders());

        Item invalidItem = new Item(4, 1000, "Computer");

        int invalidItemOrderNumber = system.addOrder(invalidItem.id(), 1);
        boolean invalidItemWasRemoved = system.removeItem(invalidItem.id());
        int invalidQuantityOrderNumber = system.addOrder(screwdriverItemId, -1);
        // My implementation is such that the last case is impossible.

        Out.println("PRINTING RESULTS OF INVALID OPERATIONS");

        Out.println(String.format("invalidItemOrderNumber: %d", invalidItemOrderNumber));
        Out.println(String.format("invalidItemWasRemoved: %b", invalidItemWasRemoved));
        Out.println(String.format("invalidQuantityOrderNumber: %d", invalidQuantityOrderNumber));
        Out.println("nullItemOrderNumber: N/A");
    }

    private static void printOrders(Order[] orders) {
        for (int i = 0; i < orders.length; i++) {
            Out.println(orders[i]);
        }

        Out.println();
    }
}
