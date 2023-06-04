package ssw.psw2.auction.common;

import com.google.gson.Gson;

import javax.websocket.*;

public class AuctionEventCoders implements Encoder.Text<AuctionEvent>, Decoder.Text<AuctionEvent> {
    private Gson gson;

    @Override
    public AuctionEvent decode(String s) throws DecodeException {
        return gson.fromJson(s, AuctionEvent.class);
    }

    @Override
    public boolean willDecode(String s) {
        return s != null;
    }

    @Override
    public String encode(AuctionEvent auctionEvent) throws EncodeException {
        return gson.toJson(auctionEvent);
    }

    @Override
    public void init(EndpointConfig endpointConfig) {
        gson = new Gson();
    }

    @Override
    public void destroy() {}
}
