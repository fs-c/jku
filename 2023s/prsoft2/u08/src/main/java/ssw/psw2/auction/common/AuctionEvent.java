package ssw.psw2.auction.common;

public class AuctionEvent {
	/**
	 * the name of the object to be sold
	 */
	public final String objectName;

	/**
	 * the current price. It is either the starting price, or the value of the last
	 * bid.
	 */
	public final double currentPrice;

	/**
	 * Specifies a client, depending on @kind
	 */
	public final String nameOfClient;

	public final Kind kind;

	AuctionEvent(String objectName, double currentPrice, String nameOfClient, Kind kind) {
		super();
		this.objectName = objectName;
		this.currentPrice = currentPrice;
		this.nameOfClient = nameOfClient;
		this.kind = kind;
	}

	public enum Kind {
		START, NEW_BID, SOLD, CANCELLED, CLIENT_JOINED, CLIENT_LEFT
	}

	public static AuctionEvent createStartEvent(String objectName, double startPrice, String highestBidder) {
		return new AuctionEvent(objectName, startPrice, highestBidder, Kind.START);
	}

	public static AuctionEvent createNewBidEvent(String objectName, double newPrice, String nameOfClient) {
		return new AuctionEvent(objectName, newPrice, nameOfClient, Kind.NEW_BID);
	}

	public static AuctionEvent createSoldEvent(String objectName, double newPrice, String nameOfClient) {
		return new AuctionEvent(objectName, newPrice, nameOfClient, Kind.SOLD);
	}

	public static AuctionEvent createClientLeftEvent(String nameOfClient) {
		return new AuctionEvent(null, 0d, nameOfClient, Kind.CLIENT_LEFT);
	}
	
	public static AuctionEvent createClientJoinedEvent(String nameOfClient) {
		return new AuctionEvent(null, 0d, nameOfClient, Kind.CLIENT_JOINED);
	}

	public static AuctionEvent createCancelEvent(String objectName) {
		return new AuctionEvent(objectName, 0d, null, Kind.CANCELLED);
	}
}
