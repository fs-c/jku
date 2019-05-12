class StockTree {
    static class Node {
        Stock stock;
        Node left, right;

        Node(Stock stock) {
            this.stock = stock;
        }
    }
}

public final class Stock {
    private int amount;
    private final String title;

    public Stock(String title, int amount) {
        this.title = title;
        this.amount = amount;
    }

    public String getTitle() {
        return title;
    }

    public int getAmount() {
        return amount;
    }

    public void increment(int value) {
        amount += value;
    }

    public String toString() {
        return String.format("[%s, %d]", title, amount);
    }
}