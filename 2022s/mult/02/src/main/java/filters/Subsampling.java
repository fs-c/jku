package filters;

import java.awt.Image;
import java.awt.image.BufferedImage;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class Subsampling implements Filter {

	@Override
	public String getFilterName() {
		return "Subsampling";
	}

	@Override
	public Image runFilter(BufferedImage image, Map<String, Parameter> parameters) {
		int rate = parameters.get("rate").getValue();
		BufferedImage bi = new BufferedImage(image.getWidth(), image.getHeight(), BufferedImage.TYPE_INT_ARGB);
	
		for (int x = 0; x < image.getWidth() - rate; x += rate) {
			for (int y = 0; y < image.getHeight() - rate; y += rate) {
				int color = image.getRGB(x, y);
				int[] colors = new int[rate];
				
				for (int i = 0; i < rate; i++) {
					colors[i] = color;
				}
				
				bi.setRGB(x, y, rate, rate, colors, 0, 0);
			}
		}
		
		return bi;
	}

	@Override
	public List<Parameter> getParameters() {
		Parameter p = new Parameter("rate", 4, 1, 8);
		return Arrays.asList(p);
	}

}
