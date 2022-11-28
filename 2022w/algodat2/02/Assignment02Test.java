package assignment02;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;


public class Assignment02Test {

    private AVLTree tree;


    public boolean insert(int key) {
        return tree.insert(key, (float) key);
    }

    @BeforeEach
    void reset() {
        tree = new AVLTree();
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testSizeProvided() {
        try {
            insert(5);
            assertEquals(1, tree.getSize(), ".getSize() is wrong after inserting a node with key 5 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(18);
            assertEquals(2, tree.getSize(), ".getSize() is wrong after inserting the nodes with key sequence "
                    + "5, 18 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(2);
            assertEquals(3, tree.getSize(), ".getSize() is wrong after inserting the nodes with key sequence "
                    + "5, 18, 2 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(8);
            assertEquals(4, tree.getSize(), ".getSize() is wrong after inserting the nodes with key sequence "
                    + "5, 18, 2, 8 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(14);
            assertEquals(5, tree.getSize(), ".getSize() is wrong after inserting the nodes with key sequence "
                    + "5, 18, 2, 8, 14 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
        } catch (Exception ex) {
            fail(".insert() or .getSize() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testSizeEmptyTree() {
        try {
            assertEquals(0, tree.getSize(), ".getSize() is wrong for empty tree: ");
        } catch (Exception ex) {
            fail(".getSize() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testSizeWithInsert() {
        try {
            assertEquals(0, tree.getSize());
            insert(5);
            assertEquals(1, tree.getSize(), ".getSize() is wrong after inserting a node with key 5 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(18);
            assertEquals(2, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(2);
            assertEquals(3, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(8);
            assertEquals(4, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(14);
            assertEquals(5, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(16);
            assertEquals(6, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(13);
            assertEquals(7, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(3);
            assertEquals(8, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(12);
            assertEquals(9, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(21);
            assertEquals(10, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(1);
            assertEquals(11, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(0);
            assertEquals(12, tree.getSize(), ".getSize() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
        } catch (Exception ex) {
            fail(".insert() or .getSize() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeightEmptyTree() {
        try {
            assertEquals(-1, tree.getTreeHeight(), ".getTreeHeight() is wrong for empty tree: ");
        } catch (Exception ex) {
            fail(".height() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeight() {
        try {
            assertEquals(-1, tree.getTreeHeight(), ".getTreeHeight() is wrong for empty tree: ");
            insert(5);
            assertEquals(0, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the node with key 5 into an empty AVL tree.\n\tTree dump:" +
                    display() + "\n\t");
            insert(18);
            assertEquals(1, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(2);
            assertEquals(1, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(8);
            assertEquals(2, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(14);
            assertEquals(2, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(16);
            assertEquals(2, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(13);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(3);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(12);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(21);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(1);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
            insert(0);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after inserting the nodes with keys "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 into an AVL tree.\n\tTree dump:" + display() + "\n\t");
        } catch (Exception ex) {
            fail(".insert() or .height() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFind() {
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            assertEquals(5f, tree.findByKey(5), ".findByKey(5) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(18f, tree.findByKey(18), ".findByKey(18) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(2f, tree.findByKey(2), ".findByKey(2) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(8f, tree.findByKey(8), ".findByKey(8) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(14f, tree.findByKey(14), ".findByKey(14) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(16f, tree.findByKey(16), ".findByKey(16) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(13f, tree.findByKey(13), ".findByKey(13) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(3f, tree.findByKey(3), ".findByKey(3) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(12f, tree.findByKey(12), ".findByKey(12) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(21f, tree.findByKey(21), ".findByKey(21) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(1f, tree.findByKey(1), ".findByKey(1) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
            assertEquals(0f, tree.findByKey(0), ".findByKey(0) didn't return correct element of the following AVL tree with \n\tthe following inserted nodes: "
                    + "5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0 \n\tTree dump:" + display() + "\n\t");
        } catch (Exception ex) {
            fail(".find() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFindNotExisting() {
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            assertEquals(-1f, tree.findByKey(4), ".findByKey() didn't return -1 when searching for a not existing key.");
            assertEquals(-1f, tree.findByKey(99), ".findByKey() didn't return -1 when searching for a not existing key.");
            assertEquals(-1f, tree.findByKey(100), ".findByKey() didn't return -1 when searching for a not existing key.");
        } catch (Exception ex) {
            fail(".find() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFindNotExistingEmptyTree() {
        try {
            assertEquals(-1f, tree.findByKey(4), ".findByKey() didn't return -1 when searching for a not existing key in an empty tree.");
            assertEquals(-1f, tree.findByKey(99), ".findByKey() didn't return -1 when searching for a not existing key in an empty tree.");
            assertEquals(-1f, tree.findByKey(100), ".findByKey() didn't return -1 when searching for a not existing key in an empty tree.");
        } catch (Exception ex) {
            fail(".find() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testRemove() {
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            assertFalse(tree.removeByKey(4), ".removeByKey(4) didn't return FALSE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
            assertFalse(tree.removeByKey(99), ".removeByKey(99) didn't return FALSE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
            assertFalse(tree.removeByKey(100), ".removeByKey(100) didn't return FALSE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");

            assertTrue(tree.removeByKey(14), ".removeByKey(14) didn't return TRUE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
            assertTrue(tree.removeByKey(3), ".removeByKey(3) didn't return TRUE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");

            assertTrue(tree.removeByKey(21), ".removeByKey(21) didn't return TRUE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
            assertTrue(tree.removeByKey(18), ".removeByKey(18) didn't return TRUE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
            assertTrue(tree.removeByKey(16), ".removeByKey(16) didn't return TRUE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");

            assertFalse((tree.removeByKey(14)), ".removeByKey(14) didn't return FALSE for the following AVL tree:\n\tTree dump:" + display() + "\n\t");
        } catch (Exception ex) {
            fail(".removeByKey() raised an exception: " + ex);
        }


    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testSizeWithRemove() {
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            StringBuilder sb = null;
            sb = display();
            tree.removeByKey(4);
            // boolean check = checkAVLIntegrity();

            // String strError = " of AVL tree broken after removing node with key 4 from the following tree:\n\tTree dump:"+sb.toString();
            // assertTrue("Integrity" + strError, check);
            // assertTrue("Height" + strError, tree.height() <= (1.44*(Math.log(tree.getSize()+2)/Math.log(2))-0.328));

            assertEquals(12, tree.getSize(), ".getSize() is wrong after removing not existing node with key 4 from the following tree:" + sb + "\n\t");

            tree.removeByKey(99);
            assertEquals(12, tree.getSize(), ".getSize() is wrong after removing not existing node with key 99 from the following tree:" + sb + "\n\t");
            tree.removeByKey(100);
            assertEquals(12, tree.getSize(), ".getSize() is wrong after removing not existing node with key 100 from the following tree:" + sb + "\n\t");

            tree.removeByKey(14);
            assertEquals(11, tree.getSize(), ".getSize() is wrong after removing node with key 14 from the following tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(3);
            assertEquals(10, tree.getSize(), ".getSize() is wrong after removing node with key 3 from the following tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(21);
            assertEquals(9, tree.getSize(), ".getSize() is wrong after removing node with key 21 from the following tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(18);
            assertEquals(8, tree.getSize(), ".getSize() is wrong after removing node with key 18 from the following tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(16);
            assertEquals(7, tree.getSize(), ".getSize() is wrong after removing node with key 16 from the following tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(14);
            assertEquals(7, tree.getSize(), ".getSize() is wrong after removing not existing node with key 14 from the following tree:" + sb + "\n\t");
        } catch (Exception ex) {
            fail(".removeByKey() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHeightWithRemove() {
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            StringBuilder sb = display();

            tree.removeByKey(4);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing not existing node with key 4 from the following AVL tree:" + sb + "\n\t");

            tree.removeByKey(99);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing not existing node with key 99 from the following AVL tree:" + sb + "\n\t");
            tree.removeByKey(100);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing not existing node with key 100 from the following AVL tree:" + sb + "\n\t");

            tree.removeByKey(14);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing node with key 14 from the following AVL tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(3);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing node with key 3 from the following AVL tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(21);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing node with key 21 from the following AVL tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(18);
            assertEquals(3, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing node with key 18 from the following AVL tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(16);
            assertEquals(2, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing node with key 16 from the following AVL tree:" + sb + "\n\t");
            sb = display();
            tree.removeByKey(14);
            assertEquals(2, tree.getTreeHeight(), ".getTreeHeight() is wrong after removing not existing node with key 14 from the following AVL tree:" + sb + "\n\t");
        } catch (Exception ex) {
            fail(".removeByKey() or .height() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testRemoveNotExistingKey() {
        try {
            assertFalse((tree.removeByKey(10212)), ".removeByKey() of a not existing key should return FALSE. ");
        } catch (Exception ex) {
            fail(".removeByKey() raised an exception: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertDuplicates() {
        reset();

        try {
            assertTrue(insert(5), ".insert() didn't return TRUE when a node with a key is inserted for the first time.");
            assertFalse(insert(5), ".insert() didn't return FALSE when a node with an already existing key is inserted.");
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }
    }


    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testToArray() {
        float[] array = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        try {
            array = tree.toArray();
        } catch (Exception ex) {
            fail(".toArray() raised an exception: " + ex);
        }
        StringBuilder sbStudentsArray = new StringBuilder();
        for (int i = 0; i < array.length; i++) {
            sbStudentsArray.append(array[i] + " ");
        }

        float[] solution = new float[]{5.0f, 2.0f, 1.0f, 0.0f, 3.0f, 14.0f, 12.0f, 8.0f, 13.0f, 18.0f, 16.0f, 21.0f};

        for (int i = 0; i < solution.length; i++)
            assertEquals(array[i], solution[i], "toArray() sequence (preorder) is wrong at idx " + i + ".\n\tYour array: [ " + sbStudentsArray + "]\n\tTree dump:"
                    + display() + "\n\t");

        // check if array is too large
        assertEquals(solution.length, array.length, "toArray() returns array with wrong size: ");
    }

    @Test
    @Timeout(value = 5000, unit = TimeUnit.MILLISECONDS)
    public void testMultipleValues() {
        int valuerange = 20;

        final int num_of_operations = 2500;  // for insert and remove
        ArrayList<String> OperationSequence = new ArrayList<String>();

        System.out.println("----------------------------------------------------------");
        System.out.println("testMultipleValues: Checking Integrity after insert/remove");
        System.out.println("----------------------------------------------------------");
        for (int i = 0; i < num_of_operations; i++) {

            boolean check = false;

            StringBuilder sbTreeBefore = null;
            StringBuilder sbTreeAfter = null;


            sbTreeBefore = display();
            int val = (int) (Math.random() * valuerange);
            try {
                if (tree.insert(val, (float) val)) {
                    OperationSequence.add(String.format(" I:%02d", val));
                } else OperationSequence.add(String.format("(I:%02d)", val));
            } catch (Exception ex) {
                fail(".insert() raised an exception: " + ex);
            }
            sbTreeAfter = display();


            check = checkAVLIntegrity();
            String strError = " of AVL tree broken after multiple insert/remove (number of operations processed: " + i + "/" + num_of_operations + ")\n\t"
                    + "--> Insert/Remove sequence (I...Insert; R...Remove; operation in brackets \"()\" was unsuccessful because of duplicate or not existing node; the very last operation caused the error):\n\t"
                    + "    ---------------------------------------------------------------------------------------------\n\t"
                    + OperationSequence + "\n\t"
                    + "\nTree before insert:\n\t" + sbTreeBefore.toString() + "\n\n\tTree after insert:" + sbTreeAfter.toString() + "\n\t";


            assertTrue(check, "Integrity" + strError);
            assertTrue(tree.getTreeHeight() <= (1.44 * (Math.log(tree.getSize() + 2) / Math.log(2)) - 0.328), "Height" + strError);


            sbTreeBefore = display();
            val = (int) (Math.random() * valuerange);
            try {
                if (tree.removeByKey(val)) {
                    OperationSequence.add(String.format(" R:%02d", val));
                } else OperationSequence.add(String.format("(R:%02d)", val));
            } catch (Exception ex) {
                fail(".removeByKey() raised an exception: " + ex);
            }
            sbTreeAfter = display();

            check = checkAVLIntegrity();

            strError = " of AVL tree broken after multiple insert/remove (number of operations processed: " + i + "/" + num_of_operations + ")\n\t"
                    + "--> Insert/Remove sequence (I...Insert; R...Remove; operation in brackets \"()\" was unsuccessful because of duplicate or not existing node; the very last operation caused the error):\n\t"
                    + "    ---------------------------------------------------------------------------------------------\n\t"
                    + OperationSequence + "\n\t"
                    + "\nTree before remove:\n\t" + sbTreeBefore.toString() + "\n\n\tTree after remove:" + sbTreeAfter.toString() + "\n\t";
            assertTrue(check, "Integrity" + strError);
            assertTrue(tree.getTreeHeight() <= (1.44 * (Math.log(tree.getSize() + 2) / Math.log(2)) - 0.328), "Height" + strError);
        }

        System.out.println("AVL integrity check successful  (number of operations processed: " + num_of_operations + ")\n\t"
                + "--> Insert/Remove sequence (I...Insert; R...Remove; operation in brackets \"()\" was unsuccessful because of duplicate or not existing node):\n\t"
//				+ "--------------------------------------------------------------------------------------------------------\n\t"
                + OperationSequence + "\n\t"
                + "\n\tFinal tree dump:" + display());
    }


    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure1() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14.";

        // test structure
        assertEquals(root.key, 5, strError);
        // left branch
        assertEquals(root.left.key, 2, strError);
        // right branch
        assertEquals(root.right.key, 14, strError);
        assertNull(root.left.left, strError);
        assertNull(root.left.right, strError);
        assertEquals(root.right.left.key, 8, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertEquals(root.right.right.key, 18, strError);
        assertNull(root.right.right.left, strError);
        assertNull(root.right.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure2() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16.";

        // test structure
        assertEquals(root.key, 14, strError);
        // left branch
        assertEquals(root.left.key, 5, strError);
        assertEquals(root.left.left.key, 2, strError);
        assertNull(root.left.left.left, strError);
        assertNull(root.left.left.right, strError);
        assertEquals(root.left.right.key, 8, strError);
        assertNull(root.left.right.left, strError);
        assertNull(root.left.right.right, strError);
        // right branch
        assertEquals(root.right.key, 18, strError);
        assertEquals(root.right.left.key, 16, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertNull(root.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure3() {
        reset();

        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16, 13.";

        // test structure
        assertEquals(root.key, 14, strError);
        // left branch
        assertEquals(root.left.key, 5, strError);
        assertEquals(root.left.left.key, 2, strError);
        assertNull(root.left.left.left, strError);
        assertNull(root.left.left.right, strError);
        assertEquals(root.left.right.key, 8, strError);
        assertNull(root.left.right.left, strError);
        assertEquals(root.left.right.right.key, 13, strError);
        assertNull(root.left.right.right.left, strError);
        assertNull(root.left.right.right.right, strError);
        // right branch
        assertEquals(root.right.key, 18, strError);
        assertEquals(root.right.left.key, 16, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertNull(root.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure4() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16, 13, 3.";

        // test structure
        assertEquals(root.key, 14, strError);
        // left branch
        assertEquals(root.left.key, 5, strError);
        assertEquals(root.left.left.key, 2, strError);
        assertNull(root.left.left.left, strError);
        assertEquals(root.left.left.right.key, 3, strError);
        assertNull(root.left.left.right.left, strError);
        assertNull(root.left.left.right.right, strError);
        assertEquals(root.left.right.key, 8, strError);
        assertNull(root.left.right.left, strError);
        assertEquals(root.left.right.right.key, 13, strError);
        assertNull(root.left.right.right.left, strError);
        assertNull(root.left.right.right.right, strError);
        // right branch
        assertEquals(root.right.key, 18, strError);
        assertEquals(root.right.left.key, 16, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertNull(root.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure5() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16, 13, 3, 12.";

        // test structure
        assertEquals(root.key, 14, strError);
        // left branch
        assertEquals(root.left.key, 5, strError);
        assertEquals(root.left.left.key, 2, strError);
        assertNull(root.left.left.left, strError);
        assertEquals(root.left.left.right.key, 3, strError);
        assertNull(root.left.left.right.left, strError);
        assertNull(root.left.left.right.right, strError);
        assertEquals(root.left.right.key, 12, strError);
        assertEquals(root.left.right.left.key, 8, strError);
        assertNull(root.left.right.left.left, strError);
        assertNull(root.left.right.left.right, strError);
        assertEquals(root.left.right.right.key, 13, strError);
        assertNull(root.left.right.right.left, strError);
        assertNull(root.left.right.right.right, strError);
        // right branch
        assertEquals(root.right.key, 18, strError);
        assertEquals(root.right.left.key, 16, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertNull(root.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure6() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16, 13, 3, 12, 21.";

        // test structure
        assertEquals(root.key, 14, strError);
        // left branch
        assertEquals(root.left.key, 5, strError);
        assertEquals(root.left.left.key, 2, strError);
        assertNull(root.left.left.left, strError);
        assertEquals(root.left.left.right.key, 3, strError);
        assertNull(root.left.left.right.left, strError);
        assertNull(root.left.left.right.right, strError);
        assertEquals(root.left.right.key, 12, strError);
        assertEquals(root.left.right.left.key, 8, strError);
        assertNull(root.left.right.left.left, strError);
        assertNull(root.left.right.left.right, strError);
        assertEquals(root.left.right.right.key, 13, strError);
        assertNull(root.left.right.right.left, strError);
        assertNull(root.left.right.right.right, strError);
        // right branch
        assertEquals(root.right.key, 18, strError);
        assertEquals(root.right.left.key, 16, strError);
        assertNull(root.right.left.left, strError);
        assertNull(root.right.left.right, strError);
        assertEquals(root.right.right.key, 21, strError);
        assertNull(root.right.right.left, strError);
        assertNull(root.right.right.right, strError);
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testStructure7() {
        AVLNode root = null;
        try {
            insert(5);
            insert(18);
            insert(2);
            insert(8);
            insert(14);
            insert(16);
            insert(13);
            insert(3);
            insert(12);
            insert(21);
            insert(1);
            insert(0);
            root = tree.getTreeRoot();
        } catch (Exception ex) {
            fail(".insert() raised an exception: " + ex);
        }

        String strError = "Rotation error after inserting the nodes with the keys 5, 18, 2, 8, 14, 16, 13, 3, 12, 21, 1, 0.";

        // test structure
        assertEquals(root.key, 5, strError);
        // left branch
        assertEquals(root.left.key, 2, strError);
        assertEquals(root.left.left.key, 1, strError);
        assertEquals(root.left.left.left.key, 0, strError);
        assertNull(root.left.left.left.left, strError);
        assertNull(root.left.left.left.right, strError);
        assertNull(root.left.left.right, strError);
        assertEquals(root.left.right.key, 3, strError);
        assertNull(root.left.right.left, strError);
        assertNull(root.left.right.right, strError);
        // right branch
        assertEquals(root.right.key, 14, strError);
        assertEquals(root.right.left.key, 12, strError);
        assertEquals(root.right.left.left.key, 8, strError);
        assertNull(root.right.left.left.left, strError);
        assertNull(root.right.left.left.right, strError);

        assertEquals(root.right.left.right.key, 13, strError);
        assertNull(root.right.left.right.left, strError);
        assertNull(root.right.left.right.right, strError);

        assertEquals(root.right.right.key, 18, strError);
        assertEquals(root.right.right.left.key, 16, strError);
        assertNull(root.right.right.left.left, strError);
        assertNull(root.right.right.left.right, strError);
        assertEquals(root.right.right.right.key, 21, strError);
        assertNull(root.right.right.right.left, strError);
        assertNull(root.right.right.right.right, strError);
    }


    //--------------------------
    // private methods


    private boolean checkAVLIntegrity() {
        return checkAVLIntegrity(tree.getTreeRoot());
    }

    private boolean checkAVLIntegrity(AVLNode n) {
        boolean isAVL = true;
        if (n == null) return true;
        if (!isAVLTree(n)) isAVL = false;

        if (!isAVL) {
            int lh = n.left == null ? -1 : n.left.height;
            int rh = n.right == null ? -1 : n.right.height;
            System.out.println(n.height + ";" + lh + ";" + rh);
        }

        if (!checkAVLIntegrity(n.left)) isAVL = false;
        if (!checkAVLIntegrity(n.right)) isAVL = false;

        return isAVL;
    }

    private boolean isAVLTree(AVLNode n) {
        int diff = (n.left == null ? -1 : n.left.height)
                - (n.right == null ? -1 : n.right.height);
        return -1 <= diff && diff <= 1;
    }

    public StringBuilder display() {
        final int height = 5, width = 64;

        int len = width * height * 2 + 2;
        StringBuilder sb = new StringBuilder(len);

        for (int i = 1; i <= len; i++)
            sb.append(i < len - 2 && i % width == 0 ? "\n" : ' ');

        displayR(sb, width / 2, 1, width / 4, width, tree.getTreeRoot(), " ");
        // System.out.println(sb);
        return sb;
    }

    private void displayR(StringBuilder sb, int c, int r, int d, int w, AVLNode n,
                          String edge) {
        if (n != null) {
            if (n != n.left)
                displayR(sb, c - d, r + 2, d / 2, w, n.left, " /");

            String s = String.valueOf(n.key);
            int idx1 = r * w + c - (s.length() + 1) / 2;
            int idx2 = idx1 + s.length();
            int idx3 = idx1 - w;
            if (idx2 < sb.length())
                sb.replace(idx1, idx2, s).replace(idx3, idx3 + 2, edge);

            if (n != n.right)
                displayR(sb, c + d, r + 2, d / 2, w, n.right, "\\ ");
        }
    }
}
