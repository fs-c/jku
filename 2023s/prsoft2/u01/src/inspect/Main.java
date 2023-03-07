package inspect;

public class Main {
    public static void main(String[] args) {
        Person alice = new Person("Alice", 45, null);
        Person bob = new Person("Bob", 52, alice);

        alice.setPartner(bob);

        Person charlie = new Person("Charlie", 16, null);

        alice.addChild(charlie);
        bob.addChild(charlie);

        Inspector inspector = new Inspector(alice);
        inspector.run();
    }
}
