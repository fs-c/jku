import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import static org.junit.jupiter.api.Assertions.*;

public class ChainingHashSetTestStudent {
    private String printHashSet(ChainingHashSet set) {
        StringBuilder sb = new StringBuilder();
        ChainingHashNode[] ht = set.getHashTable();
        for (int i = 0; i < ht.length; i++) {
            sb.append("["+i+": ");

            ChainingHashNode s = ht[i];
            if (s != null) {
                sb.append(s.key);
                ChainingHashNode cur = s.next;
                while (cur != null) {
                    sb.append("->");
                    sb.append(cur.key);
                    cur = cur.next;

                }
                sb.append("->null");
            } else {
                sb.append("null");
            }
            sb.append("]");
        }
        return sb.toString();
    }

    private ChainingHashSet fillSetWithChaining() {
        ChainingHashSet set = new ChainingHashSet(11);
        set.insert(5);
        set.insert(6);
        set.insert(7);
        set.insert(8);
        set.insert(9);
        set.insert(10);
        set.insert(11);
        set.insert(12);
        set.insert(13);
        set.insert(14);
        set.insert(15);
        set.insert(25);
        set.insert(36);
        set.insert(17);
        return set;
    }

    private ChainingHashSet fillSetWithoutChaining() {
        ChainingHashSet set = new ChainingHashSet(11);
        set.insert(5);
        set.insert(6);
        set.insert(7);
        set.insert(8);
        set.insert(9);
        set.insert(10);
        set.insert(11);
        set.insert(12);
        set.insert(13);
        set.insert(14);
        set.insert(15);
        return set;
    }

    private ChainingHashNode[] clone(ChainingHashSet set) {
        ChainingHashNode[] ht = set.getHashTable();
        ChainingHashNode[] cloneSet = new ChainingHashNode[ht.length];
        for (int i = 0; i < ht.length; i++) {
            if (ht[i] == null) continue;
            cloneSet[i] = new ChainingHashNode(ht[i].key);
            ChainingHashNode cur_set = ht[i].next;
            ChainingHashNode cur_clone = cloneSet[i];
            while (cur_set != null) {
                cur_clone.next = new ChainingHashNode(cur_set.key);
                cur_set = cur_set.next;
                cur_clone = cur_clone.next;
            }
        }
        return cloneSet;
    }

    @Test
    public void testSizeWithoutChaining() {
        ChainingHashSet solSet = new ChainingHashSet(11);
        try {
            ChainingHashSet set = new ChainingHashSet(11);
            assertEquals(0, set.size(), ".size() of empty hash set returned " + set.size() + " but should be 0");

            solSet.insert(5);
            assertTrue(set.insert(5), ".insert(5) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(1, set.size(), ".size() of empty hash set returned " + set.size() + " but should be 1set should look like this: " + printHashSet(solSet));

            solSet.insert(6);
            assertTrue(set.insert(6), ".insert(6) returned false but should be true set should look like this: " + printHashSet(solSet));
            assertEquals(2, set.size(), ".size() returned " + set.size() + " but should be 2 set should look like this: " + printHashSet(solSet));

            solSet.insert(7);
            assertTrue(set.insert(7), ".insert(7) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(3, set.size(), ".size() returned " + set.size() + " but should be 3. set should look like this: " + printHashSet(solSet));

            solSet.insert(8);
            assertTrue(set.insert(8), ".insert(8) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(4, set.size(), ".size() returned " + set.size() + " but should be 4. set should look like this: " + printHashSet(solSet));

            solSet.insert(9);
            assertTrue(set.insert(9), ".insert(9) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(5, set.size(), ".size() returned " + set.size() + " but should be 5. set should look like this: " + printHashSet(solSet));

            solSet.insert(10);
            assertTrue(set.insert(10), ".insert(10) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(6, set.size(), ".size() returned " + set.size() + " but should be 6. set should look like this: " + printHashSet(solSet));

            solSet.insert(11);
            assertTrue(set.insert(11), ".insert(11) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(7, set.size(), ".size() returned " + set.size() + " but should be 7. set should look like this: " + printHashSet(solSet));

            solSet.insert(12);
            assertTrue(set.insert(12), ".insert(12) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(8, set.size(), ".size() returned " + set.size() + " but should be 8. set should look like this: " + printHashSet(solSet));

            solSet.insert(13);
            assertTrue(set.insert(13), ".insert(13) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(9, set.size(), ".size() returned " + set.size() + " but should be 9. set should look like this: " + printHashSet(solSet));

            solSet.insert(14);
            assertTrue(set.insert(14), ".insert(14) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(10, set.size(), ".size() returned " + set.size() + " but should be 10. set should look like this: " + printHashSet(solSet));

            solSet.insert(15);
            assertTrue(set.insert(15), ".insert(15) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(11, set.size(), ".size() returned " + set.size() + " but should be 11. set should look like this: " + printHashSet(solSet));

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testSizeWithChaining() {
        ChainingHashSet solSet = new ChainingHashSet(11);

        try {
            ChainingHashSet set = new ChainingHashSet(11);
            assertEquals(0, set.size(), ".size() of empty hash set returned " + set.size() + " but should be 0");

            solSet.insert(5);
            assertTrue(set.insert(5), ".insert(5) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(1, set.size(), ".size() of empty hash set returned " + set.size() + " but should be 1set should look like this: " + printHashSet(solSet));

            solSet.insert(6);
            assertTrue(set.insert(6), ".insert(6) returned false but should be true set should look like this: " + printHashSet(solSet));
            assertEquals(2, set.size(), ".size() returned " + set.size() + " but should be 2 set should look like this: " + printHashSet(solSet));

            solSet.insert(7);
            assertTrue(set.insert(7), ".insert(7) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(3, set.size(), ".size() returned " + set.size() + " but should be 3. set should look like this: " + printHashSet(solSet));

            solSet.insert(8);
            assertTrue(set.insert(8), ".insert(8) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(4, set.size(), ".size() returned " + set.size() + " but should be 4. set should look like this: " + printHashSet(solSet));

            solSet.insert(9);
            assertTrue(set.insert(9), ".insert(9) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(5, set.size(), ".size() returned " + set.size() + " but should be 5. set should look like this: " + printHashSet(solSet));

            solSet.insert(10);
            assertTrue(set.insert(10), ".insert(10) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(6, set.size(), ".size() returned " + set.size() + " but should be 6. set should look like this: " + printHashSet(solSet));

            solSet.insert(11);
            assertTrue(set.insert(11), ".insert(11) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(7, set.size(), ".size() returned " + set.size() + " but should be 7. set should look like this: " + printHashSet(solSet));

            solSet.insert(12);
            assertTrue(set.insert(12), ".insert(12) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(8, set.size(), ".size() returned " + set.size() + " but should be 8. set should look like this: " + printHashSet(solSet));

            solSet.insert(13);
            assertTrue(set.insert(13), ".insert(13) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(9, set.size(), ".size() returned " + set.size() + " but should be 9. set should look like this: " + printHashSet(solSet));

            solSet.insert(14);
            assertTrue(set.insert(14), ".insert(14) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(10, set.size(), ".size() returned " + set.size() + " but should be 10. set should look like this: " + printHashSet(solSet));

            solSet.insert(15);
            assertTrue(set.insert(15), ".insert(15) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(11, set.size(), ".size() returned " + set.size() + " but should be 11. set should look like this: " + printHashSet(solSet));

            solSet.insert(25);
            assertTrue(set.insert(25), ".insert(25) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(12, set.size(), ".size() returned " + set.size() + " but should be 12. set should look like this: " + printHashSet(solSet));

            solSet.insert(36);
            assertTrue(set.insert(36), ".insert(36) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(13, set.size(), ".size() returned " + set.size() + " but should be 13. set should look like this: " + printHashSet(solSet));

            solSet.insert(17);
            assertTrue(set.insert(17), ".insert(17) returned false but should be true. set should look like this: " + printHashSet(solSet));
            assertEquals(14, set.size(), ".size() returned " + set.size() + " but should be 14. set should look like this: " + printHashSet(solSet));

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testInsertWithoutChaining() {
        ChainingHashSet solSet = new ChainingHashSet(11);
        try {
            ChainingHashSet studSet = new ChainingHashSet(11);

            solSet.insert(5);
            assertTrue(studSet.insert(5), ".insert(5) returned false on empty hash table but must be true.");

            assertFalse(studSet.insert(5), ".insert(5) returned true but must be false. table should look like this "+printHashSet(solSet));

            solSet.insert(7);
            assertTrue(studSet.insert(7), ".insert(7) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(8);
            assertTrue(studSet.insert(8), ".insert(8) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(9);
            assertTrue(studSet.insert(9), ".insert(9) returned false but must be true. table should look like this "+printHashSet(solSet));


            solSet.insert(10);
            assertTrue(studSet.insert(10), ".insert(10) returned false but must be true. table should look like this "+printHashSet(solSet));


            solSet.insert(6);
            assertTrue(studSet.insert(6), ".insert(6) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(11);
            assertTrue(studSet.insert(11), ".insert(11) returned false but must be true.table should look like this "+printHashSet(solSet));

            solSet.insert(12);
            assertTrue(studSet.insert(12), ".insert(12) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(13);
            assertTrue(studSet.insert(13), ".insert(13) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(14);
            assertTrue(studSet.insert(14), ".insert(14) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(15);
            assertTrue(studSet.insert(15), ".insert(15) returned false but must be true. table should look like this "+printHashSet(solSet));



            // check content
            ChainingHashNode[] hashTable = studSet.getHashTable();
            // Index 0
            assertEquals(11, hashTable[0].key, "hash table incorrect after multiple inserts. Expected 11 at index 0 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[0].next, "hash table incorrect after multiple inserts. .next at index 0 should be null but was not.Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 1
            assertEquals(12, hashTable[1].key, "hash table incorrect after multiple inserts. Expected 12 at index 1 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[1].next, "hash table incorrect after multiple inserts. .next at index 1 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 2
            assertEquals(13, hashTable[2].key, "hash table incorrect after multiple inserts. Expected 13 at index 2 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[2].next, "hash table incorrect after multiple inserts. .next at index 2 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 5
            assertEquals(5, hashTable[5].key, "hash table incorrect after multiple inserts. Expected 5 at index 5 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[5].next, "hash table incorrect after multiple inserts. .next at index 5 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 6
            assertEquals(6, hashTable[6].key, "hash table incorrect after multiple inserts. Expected 6 at index 6 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[6].next, "hash table incorrect after multiple inserts. .next at index 6 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 3
            assertEquals(14, hashTable[3].key, "hash table incorrect after multiple inserts. Index 3 should be 14 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[3].next, "hash table incorrect after multiple inserts. .next at index 3 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 4
            assertEquals(15, hashTable[4].key, "hash table incorrect after multiple inserts. Index 4 should be 15 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[4].next, "hash table incorrect after multiple inserts. .next at index 4 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 7
            assertEquals(7, hashTable[7].key, "hash table incorrect after multiple inserts. Index 7 should be 7 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[7].next, "hash table incorrect after multiple inserts. .next at index 7 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 8
            assertEquals(8, hashTable[8].key, "hash table incorrect after multiple inserts. Index 8 should be 8 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[8].next, "hash table incorrect after multiple inserts. .next at index 8 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 9
            assertEquals(9, hashTable[9].key, "hash table incorrect after multiple inserts. Index 9 should be 9 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[9].next, "hash table incorrect after multiple inserts. .next at index 9 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 10
            assertEquals(10, hashTable[10].key, "hash table incorrect after multiple inserts. Index 10 should be 10 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[10].next, "hash table incorrect after multiple inserts. .next at index 10 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testStructInsertWithChaining() {
        ChainingHashSet solSet = new ChainingHashSet(11);
        try {
            ChainingHashSet studSet = new ChainingHashSet(11);

            solSet.insert(5);
            assertTrue(studSet.insert(5), ".insert(5) returned false on empty hash table but must be true.");

            assertFalse(studSet.insert(5), ".insert(5) returned true but must be false. table should look like this "+printHashSet(solSet));

            solSet.insert(7);
            assertTrue(studSet.insert(7), ".insert(7) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(8);
            assertTrue(studSet.insert(8), ".insert(8) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(9);
            assertTrue(studSet.insert(9), ".insert(9) returned false but must be true. table should look like this "+printHashSet(solSet));


            solSet.insert(10);
            assertTrue(studSet.insert(10), ".insert(10) returned false but must be true. table should look like this "+printHashSet(solSet));


            solSet.insert(6);
            assertTrue(studSet.insert(6), ".insert(6) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(11);
            assertTrue(studSet.insert(11), ".insert(11) returned false but must be true.table should look like this "+printHashSet(solSet));

            solSet.insert(12);
            assertTrue(studSet.insert(12), ".insert(12) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(13);
            assertTrue(studSet.insert(13), ".insert(13) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(14);
            assertTrue(studSet.insert(14), ".insert(14) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(15);
            assertTrue(studSet.insert(15), ".insert(15) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(25);
            assertTrue(studSet.insert(25), ".insert(25) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(36);
            assertTrue(studSet.insert(36), ".insert(36) returned false but must be true. table should look like this "+printHashSet(solSet));

            solSet.insert(17);
            assertTrue(studSet.insert(17), ".insert(17) returned false but must be true. table should look like this "+printHashSet(solSet));


            // check content
            ChainingHashNode[] hashTable = studSet.getHashTable();
            // Index 0
            assertEquals(11, hashTable[0].key, "hash table incorrect after multiple inserts. Expected 11 at index 0 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[0].next, "hash table incorrect after multiple inserts. .next at index 0 should be null but was not.Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 1
            assertEquals(12, hashTable[1].key, "hash table incorrect after multiple inserts. Expected 12 at index 1 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[1].next, "hash table incorrect after multiple inserts. .next at index 1 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 2
            assertEquals(13, hashTable[2].key, "hash table incorrect after multiple inserts. Expected 13 at index 2 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[2].next, "hash table incorrect after multiple inserts. .next at index 2 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            //index5
            assertEquals(5, hashTable[5].key, "hash table incorrect after multiple inserts. Expected 5 at index 5 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[5].next, "hash table incorrect after multiple inserts. .next at index 5 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));
            // Index 6 (chaining)
            assertEquals(6, hashTable[6].key, "hash table incorrect after multiple inserts. Expected 6 at index 6 but did not find it. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertEquals(17, hashTable[6].next.key, "hash table incorrect after multiple inserts. .next at index 6 should be 17 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[6].next.next, "hash table incorrect after multiple inserts. .next.next at index 6 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 3 (chaining)
            assertEquals(14, hashTable[3].key, "hash table incorrect after multiple inserts. Index 3 should be 14 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertEquals(25, hashTable[3].next.key, "hash table incorrect after multiple inserts. .next at index 3 should be 25 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertEquals(36, hashTable[3].next.next.key, "hash table incorrect after multiple inserts. .next.next at index 3 should be 36 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[3].next.next.next, "hash table incorrect after multiple inserts. .next.next.next at index 3 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 4
            assertEquals(15, hashTable[4].key, "hash table incorrect after multiple inserts. Index 4 should be 15 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[4].next, "hash table incorrect after multiple inserts. .next at index 4 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 7
            assertEquals(7, hashTable[7].key, "hash table incorrect after multiple inserts. Index 7 should be 7 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[7].next, "hash table incorrect after multiple inserts. .next at index 7 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 8
            assertEquals(8, hashTable[8].key, "hash table incorrect after multiple inserts. Index 8 should be 8 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[8].next, "hash table incorrect after multiple inserts. .next at index 8 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 9
            assertEquals(9, hashTable[9].key, "hash table incorrect after multiple inserts. Index 9 should be 9 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[9].next, "hash table incorrect after multiple inserts. .next at index 9 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

            // Index 10
            assertEquals(10, hashTable[10].key, "hash table incorrect after multiple inserts. Index 10 should be 10 but was not. Table should look like this: "+printHashSet(solSet)+" but is "+printHashSet(studSet));
            assertNull(hashTable[10].next, "hash table incorrect after multiple inserts. .next at index 10 should be null but was not. Table should look like this: " + printHashSet(solSet) + " but is " + printHashSet(studSet));

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }

    }


    @Test
    public void testClearWithChaining() {
        Exception exCaught = null;
        try {
            ChainingHashSet set = new ChainingHashSet(1);
            ChainingHashSet solSet = fillSetWithChaining();
            ChainingHashNode[] hashTable = set.getHashTable();
            set.setHashTable(clone(solSet));

            assertTrue(set.size() > 0, ".size() returned incorrect value after setHashTable() using set: " + printHashSet(solSet));
            set.clear();
            assertEquals(0, set.size(), ".size() returned incorrect value after .clear() using set: " + printHashSet(solSet));

            for (int i = 0; i < hashTable.length; i++) {
                assertNull(hashTable[i], "hash table at index " + i + "must be null after .clear() but was not using hash table " + printHashSet(solSet));
            }
        } catch (Exception e) {
            exCaught = e;
        }
        assertNull(exCaught, "Some unhandled exception was raised during testing: " + exCaught);
    }

    @Test
    public void testClearWithoutChaining() {
        ChainingHashSet solSet = fillSetWithoutChaining();
        try {
            ChainingHashSet set = new ChainingHashSet(1);
            ChainingHashNode[] hashTable = set.getHashTable();
            set.setHashTable(clone(solSet));

            assertTrue(set.size() > 0, ".size() returned incorrect value after setHashTable() using set: " + printHashSet(solSet));
            set.clear();
            assertEquals(0, set.size(), ".size() returned incorrect value after .clear() using set: " + printHashSet(solSet));

            for (int i = 0; i < hashTable.length; i++) {
                assertNull(hashTable[i], "hash table at index " + i + "must be null after .clear() but was not using hash table " + printHashSet(solSet));
            }
        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }
    }


    /*additional tests*/
    @Test
    public void testSizeRemoveWithoutChaining() {
        ChainingHashSet solSet = fillSetWithoutChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);

            /*remove non-chained node*/
            assertTrue(studSet.remove(11), ".remove(11) returned False but must be true on hash table: " + printHashSet(solSet));

            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 11 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(11);

            /*remove at end of chaining list*/
            assertTrue(studSet.remove(12), ".remove(12) returned False but must be true on hash table: " + printHashSet(solSet));
            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 12 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(12);

            /*remove in mid of chaining list*/
            assertTrue(studSet.remove(13), ".remove(13) returned False but must be true on hash table: " + printHashSet(solSet));

            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 13 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(13);

            /*remove beginning of chaining list*/
            assertTrue(studSet.remove(14), ".remove(14) returned False but must be true on hash table: " + printHashSet(solSet));
            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 14 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(14);

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing: "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testSizeRemoveWithChaining() {
        ChainingHashSet solSet = fillSetWithChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);



            /*remove at end of chaining list*/
            assertTrue(studSet.remove(17), ".remove(17) returned False but must be true on hash set " +
                    printHashSet(solSet));
            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 17 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));

            solSet.remove(17);
            /*remove in mid of chaining list*/
            assertTrue(studSet.remove(25), ".remove(25) returned False but must be true on hash set " +
                    printHashSet(solSet));

            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 25 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(25);

            /*remove beginning of chaining list*/
            assertTrue(studSet.remove(14), ".remove(14) returned False but must be true hash set " +
                    printHashSet(solSet));
            assertEquals(solSet.size() - 1, studSet.size(), ".size() returned wrong size (" + studSet.size() + ") on " +
                    "remove key 14 from hash set with insert sequence " + solSet +
                    " should be " + (solSet.size() - 1));
            solSet.remove(14);

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing of .remove(): "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testStructRemoveWithoutChaining() {
        ChainingHashSet solSet = fillSetWithoutChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);

            assertTrue(studSet.remove(11), ".remove(11) returned False but must be true on hash table: " + printHashSet(solSet));

            ChainingHashNode[] stud_nodes = studSet.getHashTable();
            assertNull(stud_nodes[0], "incorrect node at index 0 after .remove(11) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            solSet.remove(11);

            assertTrue(studSet.remove(12), ".remove(17) returned False but must be true on hash table: " + printHashSet(solSet));
            stud_nodes = studSet.getHashTable();
            assertNull(stud_nodes[1], "incorrect node at index 1 after .remove(12) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            solSet.remove(12);

            assertTrue(studSet.remove(13),".remove(25) returned False but must be true on hash table: " + printHashSet(solSet));
            stud_nodes = studSet.getHashTable();
            assertNull(stud_nodes[2], "incorrect node at index 2 after .remove(13) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            solSet.remove(13);

            /*remove beginning of chaining list*/
            assertTrue(studSet.remove(14), ".remove(14) returned False but must be true on hash table: " + printHashSet(solSet));
            stud_nodes = studSet.getHashTable();
            assertNull(stud_nodes[3], "incorrect node at index 3 after .remove(14) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            solSet.remove(14);

        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing of .remove(): " +printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testStructRemoveWithChaining() {
        ChainingHashSet solSet = fillSetWithChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);




            /*remove at end of chaining list*/
            assertTrue(studSet.remove(17), ".remove(17) returned False but must be true on hash set " +
                    printHashSet(solSet));
            ChainingHashNode[] stud_nodes = studSet.getHashTable();
            assertNull(stud_nodes[6].next, "incorrect node at index 6.next after .remove(17) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            assertEquals(6, (long) (stud_nodes[6].key), "incorrect node at index 6 after .remove(17) on hash table: " + printHashSet(solSet) + " must be 6 but was not.");

            solSet.remove(17);

            /*remove in mid of chaining list*/
            assertTrue(studSet.remove(25), ".remove(25) returned False but must be true on hash set " +
                    printHashSet(solSet));
            stud_nodes = studSet.getHashTable();
            assertEquals(14, (long) (stud_nodes[3].key), "incorrect node at index 3 after .remove(25) on hash table: " + printHashSet(solSet) + " must be 14 but was not.");
            assertEquals(36, (long) (stud_nodes[3].next.key), "incorrect node at index 3.next after .remove(25) on hash table: " + printHashSet(solSet) + " must be 36 but was not.");
            assertNull(stud_nodes[3].next.next, "incorrect node at index 3.next.next after .remove(25) on hash table: " + printHashSet(solSet) + " must be null but was not.");

            solSet.remove(25);

            /*remove beginning of chaining list*/
            assertTrue(studSet.remove(14), ".remove(14) returned False but must be true on hash set " +
                    printHashSet(solSet));
            stud_nodes = studSet.getHashTable();
            assertEquals(36, (long) (stud_nodes[3].key), "incorrect node at index 3 after .remove(14) on hash table: " + printHashSet(solSet) + " must be 36 but was not.");
            assertNull(stud_nodes[3].next, "incorrect node at index 3.next after .remove(14) on hash table: " + printHashSet(solSet) + " must be null but was not.");
            solSet.remove(14);

        } catch (Exception e) {
            assertNull(e, ".remove() raised an exception on hash table: "+printHashSet(solSet)+" "+e );
        }
    }

    @Test
    public void testContainsWithChaining() {
        ChainingHashSet solSet = fillSetWithChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);

            assertTrue(studSet.contains(11), ".contains(11) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(12), ".contains(12) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(13), ".contains(13) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(14), ".contains(14) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(15), ".contains(15) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(5), ".contains(5) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(6), ".contains(6) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(7), ".contains(7) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(8), ".contains(8) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(9), ".contains(9) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(10), ".contains(10) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(25), ".contains(25) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(36), ".contains(36) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(17), ".contains(17) returned false but must be true for hash table: " + printHashSet(solSet));
            assertFalse(studSet.contains(18), ".contains(18) returned true but must be false for hash table: " + printHashSet(solSet));
        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing of .contains(): "+printHashSet(solSet)+" "+e);
        }
    }


    @Test
    public void testContainsWithoutChaining() {
        ChainingHashSet solSet = fillSetWithoutChaining();
        try {
            ChainingHashSet studSet = new ChainingHashSet(1);
            ChainingHashNode[] sol_copy = clone(solSet);
            studSet.setHashTable(sol_copy);

            assertTrue(studSet.contains(11), ".contains(11) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(12), ".contains(12) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(13), ".contains(13) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(14), ".contains(14) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(15), ".contains(15) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(5), ".contains(5) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(6), ".contains(6) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(7), ".contains(7) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(8), ".contains(8) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(9), ".contains(9) returned false but must be true for hash table: " + printHashSet(solSet));
            assertTrue(studSet.contains(10), ".contains(10) returned false but must be true for hash table: " + printHashSet(solSet));
            assertFalse(studSet.contains(18), ".contains(18) returned true but must be false for hash table: " + printHashSet(solSet));


        } catch (Exception e) {
            assertNull(e, "Some unhandled exception was raised during testing of .contains(): "+printHashSet(solSet)+" "+e);
        }
    }

    @Test
    public void testRemoveNonExisting() {
        ChainingHashSet studSet = new ChainingHashSet(11);
        assertFalse(studSet.remove(1), "remove(1) on empty hash table returned true but must be false");
    }

    @Test
    public void testContainsFalse() {
        ChainingHashSet studSet = new ChainingHashSet(11);
        assertFalse(studSet.contains(1), "contains(1) on empty hash table returned true but must be false");
    }

}