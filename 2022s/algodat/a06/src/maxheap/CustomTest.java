package maxheap;

public class CustomTest {
    public static void main(String[] args) {
        test(new int[]{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 });
    }

    private static void test(int[] arr) {
        print(arr);

        MaxHeap heap = new MaxHeap(arr);
        print(heap.getHeap());

        MaxHeap.sort(arr);
        print(arr);
    }

    private static void print(int[] arr) {
        System.out.print("\t{ ");

        for (int j : arr) {
            System.out.format("%d ", j);
        }

        System.out.println("}");
    }
}
