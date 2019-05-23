import java.io.*;

public class ListOfNumbers {

    private static final int CAPACITY = 10;
    private int[] values;

    public ListOfNumbers() {
        values = new int[CAPACITY];
        for (int i = 0; i < CAPACITY; i++)
            values[i] = i;
    }

    public void writeList(String fileName) throws IOException {
        // JDK >= 7, try-with-resources-statement
        try (BufferedWriter out = new BufferedWriter(new FileWriter(fileName))) {            
            for (int i = 0; i < CAPACITY; i++) {
                int value = values[i];

                out.write("Value " + value + " written to file");

                out.newLine();
            }
        } catch (IOException e) {
            throw e;
        }
    }
}
