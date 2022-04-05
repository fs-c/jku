package filters;

import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/** Interface to be implemented by all Filters */
public interface Filter {
  String getFilterName();

  Image runFilter(BufferedImage image, Map<String, Parameter> parameters);

  List<Parameter> getParameters();

  default Map<String, Parameter> getParametersMap() {
    return getParameters().stream()
        .collect(Collectors.toMap(Parameter::getName, Function.identity()));
  }
}
