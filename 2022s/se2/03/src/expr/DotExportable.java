package expr;

public interface DotExportable {
    String NODE_FORMAT = "%s [label=\"%s\\n%.2f\", shape=\"%s\", style=\"filled\", fillcolor=\"%s\"];\n";
    String LINE_FORMAT = "%s -> %s;\n";
    String DASHED_LINE_FORMAT = "%s -> %s [style=\"dashed\"];\n";

    static String formatNode(int id, String label, double value, String shape, String color) {
        return String.format(NODE_FORMAT, id, label, value, shape, color);
    }

    static String formatLine(int fromId, int toId, boolean dashed) {
        return String.format(dashed ? DASHED_LINE_FORMAT : LINE_FORMAT, fromId, toId);
    }

    String asDotString(boolean useDashedEdges);

    default String asDotString() {
        return asDotString(false);
    }
}
