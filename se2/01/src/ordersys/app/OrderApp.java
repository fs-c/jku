package ordersys.app;

import inout.Out;

import ordersys.Item;
import ordersys.Order;
import ordersys.Status;
import ordersys.OrderSystem;

public class OrderApp {

    public static void main(String[] args) {
        OrderSystem system = new OrderSystem();

        Item screw = new Item(0, 2.5, "100pcs M2 8mm Screws");
        Item screwdriver = new Item(1, 7, "Simple Screwdriver");
        Item nails = new Item(2, 2, "20pcs 40mm Nails");
        Item hammer = new Item(3, 15, "Simple Hammer");

        // TODO: add all 4 items to the system

        // TODO: perform the following orders using the ordersystem
        // ITEM         | QUANTITY
        // screw        | 10
        // screwdriver  | 2
        // nails (1st)  | 1
        // nails (2nd)  | 1
        // hammer       | 1

        Out.println("PRINTING ORDERS AFTER PART 1:");
        // TODO: print all orders using the "printOrders" method

        // TODO: set the status of the scre order to cancelled

        // TODO: perform a new order of scews, however with a quantity of 1

        // TODO: set the status of the orders as follows:
        // ORDER        |   STATUS
        // screwdriver  |   PROCESSING
        // NAIL (1st)   |   FULFILLED
        // NAIL (2nd)   |   PROCESSING
        // HAMMER       |   FULFILLED

        Out.println("PRINTING ORDERS AFTER PART 2:");
        // TODO: print all orders using the "printOrders" method

        Out.println("PRINTING ALL FULFILLED ORDERS:");
        // TODO: print all fulfilled orders

        Out.println("PRINTING ALL ORDERS OF NAILS:");
        // TODO: print all order of nails

        Out.println("PRINTING ALL OPEN ORDERS");
        // TODO: print all open orders

        Item invalidItem = new Item(4, 1000, "Computer");
        // TODO: check that you implementation does not allow invalid operations
        // perform an order with the invalid item
        // remove the invalid item from the system
        // create an order (using the order system) with the screwdriver and a quantity of -1
        // create an order (using the order system) with a "null" item and a quantity of -1

        Out.println("PRINTING RESULTS OF INVALID OPERATIONS");
        // TODO: print the order numbers of the invalid operations from above, one per line
    }

    private static void printOrders(Order[] orders) {
        for (int i = 0; i < orders.length; i++) {
            Out.println(orders[i]);
        }

        Out.println();
    }

}
