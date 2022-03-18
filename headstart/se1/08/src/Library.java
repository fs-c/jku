final class Library {
    public static void main(String args[]) {
        final var st = new StockTree();

        In.open(args[0]);

        while (!In.isEof()) {
            final int amount = In.readInt();

            st.insert(In.readLine(), amount);
        }

        final int a1 = st.amount("Promises Kept");

        Out.format("%d%n", a1);

        st.printOrdered();
    }
}

final class StockTree {
    static final class Node {
        Stock stock;
        Node left = null, right = null;

        Node(Stock stock) {
            this.stock = stock;
        }

        public void insert(Node node) {
            final int order = node.stock.getTitle()
                .compareTo(this.stock.getTitle());

            if (order < 0) {
                if (left == null)
                    left = node;
                else
                    left.insert(node);
            } else if (order > 0) {
                if (right == null)
                    right = node;
                else
                    right.insert(node);
            } else {
                this.stock.increment(1);
            }
        }

        public Stock find(String title) {
            final int order = title.compareTo(this.stock.getTitle());

            Out.format("order: %d%n", order);

            if (order == 0)
                return this.stock;

            if (order < 0) {
                if (left != null)
                    return left.find(title);
            } else {
                if (right != null)
                    return right.find(title);
            }

            return null;
        }

        @Override
        public String toString() {
            return String.format("%d %s", this.stock.getAmount(),
                this.stock.getTitle());
        }
    }

    Node root = null;

    public void insert(String title, int amount) {
        final var nn = new Node(new Stock(title, amount));

        if (root == null)
            root = nn;

        root.insert(nn);
    }

    public int amount(String title) {
        final var item = root.find(title);

        return item == null ? 0 : item.getAmount();
    }

    public void printOrdered() {
        printOrdered(root);
    }

    private void printOrdered(Node node) {
        if (node.left != null)
            printOrdered(node.left);

        Out.println(node.toString());

        if (node.right != null)
            printOrdered(node.right);
    }
}

final class Stock {
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