package transport;

public class TankTruck extends Transporter {
    public TankTruck(String name, int maxLoadWeight, int costPerKilometre, Location currentLocatiom) {
        super(name, maxLoadWeight, costPerKilometre, new Cargo.Type[]{ Cargo.Type.LIQUID }, canTraverseOcean, currentLocatiom);
    }
}
