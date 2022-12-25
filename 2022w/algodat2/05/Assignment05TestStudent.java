import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;

import static org.junit.jupiter.api.Assertions.*;

public class Assignment05TestStudent {
    private JKUMap map = null;

    @BeforeEach
    private void init() {
        map = new JKUMap();
    }

    @Test
    public void testMapConstruction() {
        try {
            String warning = " MAKE SURE TO FIX THIS, OTHERWISE ALL OTHER TESTS CANNOT WORK!";

            assertEquals(17, map.getNumberOfVertices(), ".getNumberOfVertices() did return a wrong count." + warning);
            assertNotNull(map.findVertex("SP3"), ".findVertex() did not find SP3." + warning);
            assertNotNull(map.findVertex("SP1"), ".findVertex() did not find SP1." + warning);
            assertNotNull(map.findVertex("Parking"), ".findVertex() did not find Parking." + warning);
            assertNotNull(map.findVertex("LUI"), ".findVertex() did not find LUI." + warning);
            assertNotNull(map.findVertex("Teichwerk"), ".findVertex() did not find Teichwerk." + warning);
            assertNotNull(map.findVertex("Bella Casa"), ".findVertex() did not find Bella Casa." + warning);
            assertNotNull(map.findVertex("Chat"), ".findVertex() did not find Chat." + warning);
            assertNotNull(map.findVertex("Library"), ".findVertex() did not find Library." + warning);
            assertNotNull(map.findVertex("Bank"), ".findVertex() did not find Bank." + warning);
            assertNotNull(map.findVertex("KHG"), ".findVertex() did not find SP3." + warning);
            assertNotNull(map.findVertex("Spar"), ".findVertex() did not find Spar." + warning);
            assertNotNull(map.findVertex("Porter"), ".findVertex() did not find Porter." + warning);
            assertNotNull(map.findVertex("Open Lab"), ".findVertex() did not find Open Lab." + warning);
            assertNotNull(map.findVertex("LIT"), ".findVertex() did not find LIT." + warning);
            assertNotNull(map.findVertex("Castle"), ".findVertex() did not find Castle." + warning);
            assertNotNull(map.findVertex("Papaya"), ".findVertex() did not find Papaya." + warning);
            assertNotNull(map.findVertex("JKH"), ".findVertex() did not find JHK." + warning);

            assertEquals(19, map.getNumberOfEdges(), ".getNumberOfEdges() did return a wrong count." + warning);

            assertNotNull(map.findEdge("SP1", "SP3"), ".findEdge() did not find edge between SP1 and SP3." + warning);
            assertNotNull(map.findEdge("SP3", "SP1"), ".findEdge() did not find edge between SP3 and SP1." + warning);
            assertEquals(130, map.findEdge("SP3", "SP1").weight, ".findEdge() returned wrong edge weight for edge between SP3 and SP1." + warning);

            assertNotNull(map.findEdge("SP1", "LUI"), ".findEdge() did not find edge between SP1 and LUI." + warning);
            assertNotNull(map.findEdge("LUI", "SP1"), ".findEdge() did not find edge between LUI and SP1." + warning);
            assertEquals(175, map.findEdge("LUI", "SP1").weight, ".findEdge() returned wrong edge weight for edge between LUI and SP1." + warning);

            assertNotNull(map.findEdge("SP1", "Parking"), ".findEdge() did not find edge between SP1 and Parking." + warning);
            assertNotNull(map.findEdge("Parking", "SP1"), ".findEdge() did not find edge between Parking and SP1." + warning);
            assertEquals(240, map.findEdge("Parking", "SP1").weight, ".findEdge() returned wrong edge weight for edge between Parking and SP1." + warning);

            assertNotNull(map.findEdge("Bella Casa", "Parking"), ".findEdge() did not find edge between Bella Casa and Parking." + warning);
            assertNotNull(map.findEdge("Parking", "Bella Casa"), ".findEdge() did not find edge between Parking and Bella Casa." + warning);
            assertEquals(145, map.findEdge("Parking", "Bella Casa").weight, ".findEdge() returned wrong edge weight for edge between Parking and Bella Casa." + warning);

            assertNotNull(map.findEdge("KHG", "Parking"), ".findEdge() did not find edge between KHG and Parking." + warning);
            assertNotNull(map.findEdge("Parking", "KHG"), ".findEdge() did not find edge between Parking and KHG." + warning);
            assertEquals(190, map.findEdge("Parking", "KHG").weight, ".findEdge() returned wrong edge weight for edge between Parking and KHG." + warning);

            assertNotNull(map.findEdge("KHG", "Spar"), ".findEdge() did not find edge between KHG and Spar." + warning);
            assertNotNull(map.findEdge("Spar", "KHG"), ".findEdge() did not find edge between Spar and KHG." + warning);
            assertEquals(165, map.findEdge("Spar", "KHG").weight, ".findEdge() returned wrong edge weight for edge between Spar and KHG." + warning);

            assertNotNull(map.findEdge("KHG", "Bank"), ".findEdge() did not find edge between KHG and Bank." + warning);
            assertNotNull(map.findEdge("Bank", "KHG"), ".findEdge() did not find edge between Bank and KHG." + warning);
            assertEquals(150, map.findEdge("Bank", "KHG").weight, ".findEdge() returned wrong edge weight for edge between Bank and KHG." + warning);

            assertNotNull(map.findEdge("Porter", "Spar"), ".findEdge() did not find edge between Porter and Spar." + warning);
            assertNotNull(map.findEdge("Spar", "Porter"), ".findEdge() did not find edge between Spar and Porter." + warning);
            assertEquals(103, map.findEdge("Spar", "Porter").weight, ".findEdge() returned wrong edge weight for edge between Spar and Porter." + warning);

            assertNotNull(map.findEdge("LIT", "Spar"), ".findEdge() did not find edge between LIT and Spar." + warning);
            assertNotNull(map.findEdge("Spar", "LIT"), ".findEdge() did not find edge between Spar and LIT." + warning);
            assertEquals(50, map.findEdge("Spar", "LIT").weight, ".findEdge() returned wrong edge weight for edge between Spar and LIT." + warning);

            assertNotNull(map.findEdge("LIT", "Porter"), ".findEdge() did not find edge between LIT and Porter." + warning);
            assertNotNull(map.findEdge("Porter", "LIT"), ".findEdge() did not find edge between Porter and LIT." + warning);
            assertEquals(80, map.findEdge("Porter", "LIT").weight, ".findEdge() returned wrong edge weight for edge between Porter and LIT." + warning);

            assertNotNull(map.findEdge("Open Lab", "Porter"), ".findEdge() did not find edge between Open Lab and Porter." + warning);
            assertNotNull(map.findEdge("Porter", "Open Lab"), ".findEdge() did not find edge between Porter and Open Lab." + warning);
            assertEquals(70, map.findEdge("Porter", "Open Lab").weight, ".findEdge() returned wrong edge weight for edge between Porter and Open Lab." + warning);

            assertNotNull(map.findEdge("Bank", "Porter"), ".findEdge() did not find edge between Bank and Porter." + warning);
            assertNotNull(map.findEdge("Porter", "Bank"), ".findEdge() did not find edge between Porter and Bank." + warning);
            assertEquals(100, map.findEdge("Porter", "Bank").weight, ".findEdge() returned wrong edge weight for edge between Porter and Bank." + warning);

            assertNotNull(map.findEdge("Bank", "Chat"), ".findEdge() did not find edge between Bank and Chat." + warning);
            assertNotNull(map.findEdge("Chat", "Bank"), ".findEdge() did not find edge between Chat and Bank." + warning);
            assertEquals(115, map.findEdge("Chat", "Bank").weight, ".findEdge() returned wrong edge weight for edge between Chat and Bank." + warning);

            assertNotNull(map.findEdge("Library", "Chat"), ".findEdge() did not find edge between Library and Chat." + warning);
            assertNotNull(map.findEdge("Chat", "Library"), ".findEdge() did not find edge between Chat and Library." + warning);
            assertEquals(160, map.findEdge("Chat", "Library").weight, ".findEdge() returned wrong edge weight for edge between Chat and Library." + warning);

            assertNotNull(map.findEdge("LUI", "Chat"), ".findEdge() did not find edge between LUI and Chat." + warning);
            assertNotNull(map.findEdge("Chat", "LUI"), ".findEdge() did not find edge between Chat and LUI." + warning);
            assertEquals(240, map.findEdge("Chat", "LUI").weight, ".findEdge() returned wrong edge weight for edge between Chat and LUI." + warning);

            assertNotNull(map.findEdge("Library", "LUI"), ".findEdge() did not find edge between Library and LUI." + warning);
            assertNotNull(map.findEdge("LUI", "Library"), ".findEdge() did not find edge between LUI and Library." + warning);
            assertEquals(90, map.findEdge("LUI", "Library").weight, ".findEdge() returned wrong edge weight for edge between LUI and Library." + warning);

            assertNotNull(map.findEdge("Teichwerk", "LUI"), ".findEdge() did not find edge between Teichwerk and LUI." + warning);
            assertNotNull(map.findEdge("LUI", "Teichwerk"), ".findEdge() did not find edge between LUI and Teichwerk." + warning);
            assertEquals(135, map.findEdge("LUI", "Teichwerk").weight, ".findEdge() returned wrong edge weight for edge between LUI and Teichwerk." + warning);

            assertNotNull(map.findEdge("Castle", "Papaya"), ".findEdge() did not find edge between Castle and Papaya." + warning);
            assertNotNull(map.findEdge("Papaya", "Castle"), ".findEdge() did not find edge between Papaya and Castle." + warning);
            assertEquals(85, map.findEdge("Papaya", "Castle").weight, ".findEdge() returned wrong edge weight for edge between Papaya and Castle." + warning);

            assertNotNull(map.findEdge("JKH", "Papaya"), ".findEdge() did not find edge between JKH and Papaya." + warning);
            assertNotNull(map.findEdge("Papaya", "JKH"), ".findEdge() did not find edge between Papaya and JKH." + warning);
            assertEquals(80, map.findEdge("Papaya", "JKH").weight, ".findEdge() returned wrong edge weight for edge between Papaya and JKH." + warning);
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testNonExisitingShortestPathFromJKHToKHG() {
        try {
            ArrayList<Step> path = map.getShortestPathFromTo(map.findVertex("JKH"), map.findVertex("KHG"));
            assertNull(path, ".getShortestPathFromTo() did not return null for a non-existing way from JKH to KHG");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testNonExisitingShortestPathFromKHGToJKH() {
        try {
            ArrayList<Step> path = map.getShortestPathFromTo(map.findVertex("KHG"), map.findVertex("JKH"));
            assertNull(path, ".getShortestPathFromTo() did not return null for a non-existing way from KHG to JKH");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testExisitingShortestPathFromCastleToPapaya() {
        try {
            ArrayList<Step> path = map.getShortestPathFromTo(map.findVertex("Castle"), map.findVertex("Papaya"));
            assertNotNull(path, ".getShortestPathFromTo() did return null for an existing way from Castle to Papaya");
            assertEquals("Castle", path.get(0).point.name);
            assertEquals(0, path.get(0).coveredDistance);
            assertEquals("Papaya", path.get(1).point.name);
            assertEquals(85, path.get(1).coveredDistance);
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testExisitingShortestPathFromSP3ToSpar() {
        try {
            ArrayList<Step> path = map.getShortestPathFromTo(map.findVertex("SP3"), map.findVertex("Spar"));
            assertNotNull(path, ".getShortestPathFromTo() did return null for an existing way from SP3 to Spar");
            assertEquals("SP3", path.get(0).point.name);
            assertEquals(0, path.get(0).coveredDistance);
            assertEquals("SP1", path.get(1).point.name);
            assertEquals(130, path.get(1).coveredDistance);
            assertEquals("Parking", path.get(2).point.name);
            assertEquals(370, path.get(2).coveredDistance);
            assertEquals("KHG", path.get(3).point.name);
            assertEquals(560, path.get(3).coveredDistance);
            assertEquals("Spar", path.get(4).point.name);
            assertEquals(725, path.get(4).coveredDistance);
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testShortestDistancesFromJKH() {
        try {
            HashMap<String, Integer> res = map.getShortestDistancesFrom(map.findVertex("JKH"));

            assertEquals(17, res.size(), ".getShortestDistancesFrom() returned a map with a wrong number of entries.");
            assertEquals(165, res.get("Castle"), ".getShortestDistancesFrom() did return wrong distance for reachable point");
            assertEquals(80, res.get("Papaya"), ".getShortestDistancesFrom() did return wrong distance for reachable point");

            assertEquals(0, res.get("JKH"), ".getShortestDistancesFrom() did not return 0 for the start point");

            assertEquals(-1, res.get("LUI"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Library"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Chat"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Teichwerk"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("SP1"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("SP3"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Parking"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Bank"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Bella Casa"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("KHG"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Porter"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Spar"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("LIT"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Open Lab"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testShortestDistancesFromLUI() {
        try {
            HashMap<String, Integer> res = map.getShortestDistancesFrom(map.findVertex("LUI"));

            assertEquals(17, res.size(), ".getShortestDistancesFrom() returned a map with a wrong number of entries.");
            assertEquals(-1, res.get("Castle"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Papaya"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("JKH"), ".getShortestDistancesFrom() did not return -1 for a non-reachable point");

            assertEquals(0, res.get("LUI"), ".getShortestDistancesFrom() did not return 0 for the start point");

            assertEquals(90, res.get("Library"), ".getShortestDistancesFrom() did return a wrong distance for a direct neighbor");
            assertEquals(240, res.get("Chat"), ".getShortestDistancesFrom() did return a wrong distance for a direct neighbor");
            assertEquals(135, res.get("Teichwerk"), ".getShortestDistancesFrom() did return a wrong distance for a direct neighbor");
            assertEquals(175, res.get("SP1"), ".getShortestDistancesFrom() did return a wrong distance for a direct neighbor");

            assertEquals(305, res.get("SP3"), ".getShortestDistancesFrom() did return a wrong distance for a 2-step reachable point");
            assertEquals(415, res.get("Parking"), ".getShortestDistancesFrom() did return a wrong distance for a 2-step reachable point");
            assertEquals(355, res.get("Bank"), ".getShortestDistancesFrom() did return a wrong distance for a 2-step reachable point");

            assertEquals(560, res.get("Bella Casa"), ".getShortestDistancesFrom() did return a wrong distance for a 3-step reachable point");
            assertEquals(505, res.get("KHG"), ".getShortestDistancesFrom() did return a wrong distance for a 3-step reachable point");
            assertEquals(455, res.get("Porter"), ".getShortestDistancesFrom() did return a wrong distance for a 3-step reachable point");

            assertEquals(558, res.get("Spar"), ".getShortestDistancesFrom() did return a wrong distance for a 4-step reachable point");
            assertEquals(535, res.get("LIT"), ".getShortestDistancesFrom() did return a wrong distance for a 4-step reachable point");
            assertEquals(525, res.get("Open Lab"), ".getShortestDistancesFrom() did return a wrong distance for a 4-step reachable point");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testStepsOnShortestPathsFromJKH() {
        try {
            HashMap<String, Integer> res = map.getStepsForShortestPathsFrom(map.findVertex("JKH"));

            assertEquals(17, res.size(), ".getStepsOnShortestPathsFrom() returned a map with a wrong number of entries.");
            assertEquals(0, res.get("JKH"), ".getStepsOnShortestPathsFrom() did not return 0 for the start point");
            assertEquals(1, res.get("Papaya"), ".getStepsOnShortestPathsFrom() did return wrong step count for reachable point");
            assertEquals(2, res.get("Castle"), ".getStepsOnShortestPathsFrom() did return wrong step count for reachable point");

            assertEquals(-1, res.get("LUI"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Library"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Chat"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Teichwerk"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("SP1"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("SP3"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Parking"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Bank"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Bella Casa"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("KHG"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Porter"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Spar"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("LIT"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Open Lab"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testStepsOnShortestPathsFromLUI() {
        try {
            HashMap<String, Integer> res = map.getStepsForShortestPathsFrom(map.findVertex("LUI"));

            assertEquals(17, res.size(), ".getStepsOnShortestPathsFrom() returned a map with a wrong number of entries.");
            assertEquals(-1, res.get("Castle"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("Papaya"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");
            assertEquals(-1, res.get("JKH"), ".getStepsOnShortestPathsFrom() did not return -1 for a non-reachable point");

            assertEquals(0, res.get("LUI"), ".getStepsOnShortestPathsFrom() did not return 0 for the start point");

            assertEquals(1, res.get("Library"), ".getStepsOnShortestPathsFrom() did not return 1 for a direct neighbor");
            assertEquals(1, res.get("Chat"), ".getStepsOnShortestPathsFrom() did not return 1 for a direct neighbor");
            assertEquals(1, res.get("Teichwerk"), ".getStepsOnShortestPathsFrom() did not return 1 for a direct neighbor");
            assertEquals(1, res.get("SP1"), ".getStepsOnShortestPathsFrom() did not return 1 for a direct neighbor");

            assertEquals(2, res.get("SP3"), ".getStepsOnShortestPathsFrom() did not return 2 for a 2-step reachable point");
            assertEquals(2, res.get("Parking"), ".getStepsOnShortestPathsFrom() did not return 2 for a 2-step reachable point");
            assertEquals(2, res.get("Bank"), ".getStepsOnShortestPathsFrom() did not return 2 for a 2-step reachable point");

            assertEquals(3, res.get("Bella Casa"), ".getStepsOnShortestPathsFrom() did not return 3 for a 3-step reachable point");
            assertEquals(3, res.get("KHG"), ".getStepsOnShortestPathsFrom() did not return 3 for a 3-step reachable point");
            assertEquals(3, res.get("Porter"), ".getStepsOnShortestPathsFrom() did not return 3 for a 3-step reachable point");

            assertEquals(4, res.get("Spar"), ".getStepsOnShortestPathsFrom() did not return 4 for a 4-step reachable point");
            assertEquals(4, res.get("LIT"), ".getStepsOnShortestPathsFrom() did not return 4 for a 4-step reachable point");
            assertEquals(4, res.get("Open Lab"), ".getStepsOnShortestPathsFrom() did not return 4 for a 4-step reachable point");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testShortestPathFromToNullParameter() {
        try {
            assertThrows(IllegalArgumentException.class, () -> map.getShortestPathFromTo(null, map.findVertex("LUI")), ".getShortestPathFromTo() did not throw an expected " +
                    "IllegalArgumentException when null was passed as parameter");
            assertThrows(IllegalArgumentException.class, () -> map.getShortestPathFromTo(map.findVertex("LUI"), null), ".getShortestPathFromTo() did not throw an expected " +
                    "IllegalArgumentException when null was passed as parameter");
            assertThrows(IllegalArgumentException.class, () -> map.getShortestPathFromTo(null, null), ".getShortestPathFromTo() did not throw an expected " +
                    "IllegalArgumentException when null was passed as parameter");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testShortestPathFromToSameParameter() {
        try {
            assertThrows(IllegalArgumentException.class, () -> map.getShortestPathFromTo(map.findVertex("LUI"), map.findVertex("LUI")), ".getShortestPathFromTo() did not throw an expected " +
                    "IllegalArgumentException when the same vertex was passed for both parameters");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    public void testStepsOnShortestPathsFromNullParameter() {
        try {
            assertThrows(IllegalArgumentException.class, () -> map.getStepsForShortestPathsFrom(null), ".getStepsOnShortestPathsFrom() did not throw an expected " +
                    "IllegalArgumentException when null was passed as parameter");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }


    @Test
    public void testShortestDistancesFromNullParameter() {
        try {
            assertThrows(IllegalArgumentException.class, () -> map.getShortestDistancesFrom(null), ".getShortestDistancesFrom() did not throw an expected " +
                    "IllegalArgumentException when null was passed as parameter");
        }  catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }
}
