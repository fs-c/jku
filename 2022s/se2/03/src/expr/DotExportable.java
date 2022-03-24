package expr;

public interface DotExportable {
    protected static final String

    String asDotString(boolean useDashedEdges);

    default String asDotString() {
        return asDotString(false);
    }
}
