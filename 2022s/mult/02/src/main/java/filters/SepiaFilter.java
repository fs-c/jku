package filters;

import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import pixels.Pixel;

public class SepiaFilter implements Filter {

	@Override
	public String getFilterName() {
		return "Sepia Filter";
	}

	@Override
	public Image runFilter(BufferedImage image, Map<String, Parameter> parameters) {
	    BufferedImage bi = new BufferedImage(image.getWidth(), image.getHeight(), image.getType());
	
	    for (int x = 0; x < image.getWidth(); x++) {
			for (int y = 0; y < image.getHeight(); y++) {
				Pixel p = new Pixel(image.getRGB(x, y));

				int red = p.getR(), green = p.getG(), blue = p.getB();
				
				bi.setRGB(x, y, Pixel.generateRaw(
					(int)((red * 0.393) + (green * 0.768) + (blue * 0.189)),
					(int)((red * 0.349) + (green * 0.686) + (blue * 0.168)),
					(int)((red * 0.272) + (green * 0.534) + (blue * 0.131)),
					p.getAlpha()
				));
			}
		}
	    
		return bi;

	}

	@Override
	public List<Parameter> getParameters() {
		return Arrays.asList();
	}
}
