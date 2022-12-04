import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.extension.ExtendWith;

import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;
public class Assignment04TestStudents {

    private G map;

    @BeforeEach
    public void setup() {
        map = new G();
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertVertex() {
        try {
            V linz = map.insertVertex("Linz");
            assertEquals(linz.idx, 0, ".insertVertex() returned wrong vertex index after inserting vertex \"Linz\" into an empty graph: ");
            assertEquals(linz.name, "Linz", ".insertVertex() returned wrong vertex name after inserting vertex \"Linz\" into an empty graph: ");
            assertEquals(linz, map.vertices[linz.idx], ".insertVertex(): wrong vertex at index 0 after inserting vertices \"Linz\" into an empty graph: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testDoubleInsertVertex() {
        try {
            V linz = map.insertVertex("Linz");
            V linz2 = map.insertVertex("Linz");
            assertNull(linz2, ".insertVertex() returned not null on already existing vertex: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertMultipleVertices() {
        try {
            V linz = map.insertVertex("Linz");
            assertEquals(0, linz.idx, ".insertVertex() returned wrong vertex index after inserting vertex \"Linz\" into an empty graph: ");
            assertEquals(linz, map.vertices[linz.idx], ".insertVertex(): wrong vertex at index 0 after inserting vertices \"Linz\" into an empty graph: ");

            V wien = map.insertVertex("Wien");
            assertEquals(1, wien.idx, ".insertVertex() returned wrong index for \"Wien\" after inserting vertex \"Linz\" and \"Wien\" into an empty graph: ");
            assertEquals(linz, map.vertices[linz.idx], ".insertVertex(): wrong vertex at index 0 after inserting vertices \"Linz\" and \"Wien\" into an empty graph: ");
            assertEquals(wien, map.vertices[wien.idx], ".insertVertex(): wrong vertex at index 1 after inserting vertices \"Linz\" and \"Wien\" into an empty graph: ");

            V graz = map.insertVertex("Graz");
            assertEquals(2, graz.idx, ".insertVertex() returned wrong index for \"Graz\" after inserting vertex \"Linz\", \"Wien\" and \"Graz\" into an empty graph: ");
            assertEquals(linz, map.vertices[linz.idx], ".insertVertex(): wrong vertex at index 0 after inserting vertices \"Linz\", \"Wien\" and \"Graz\" into an empty graph: ");
            assertEquals(wien, map.vertices[wien.idx], ".insertVertex(): wrong vertex at index 1 after inserting vertices \"Linz\", \"Wien\" and \"Graz\" into an empty graph: ");
            assertEquals(graz, map.vertices[graz.idx], ".insertVertex(): wrong vertex at index 2 after inserting vertices \"Linz\", \"Wien\" and \"Graz\" into an empty graph: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testGetNumberOfEdgesLarge() {
        try {
            map = initializeLargeGraph();
            assertEquals(16, map.getNumberOfEdges(), ".getNumberOfEdges() returned wrong value for a graph with 16 edges: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testGetNumberOfVerticesLarge() {
        try {
            map = initializeLargeGraph();
            assertEquals(18, map.getNumberOfVertices(), ".getNumberOfVertices() returned wrong value for a graph with 18 vertices: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }


    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertNotYetExistingEdges() {
        try {
            map.insertVertex("Linz");
            map.insertVertex("Wien");
            map.insertVertex("Graz");
            String strGraph = "[\"Linz\",\"Wien\",\"Graz\"]";

            assertNotNull(map.insertEdge("Linz", "Wien", 100), ".insertEdge(): inserting a not existing edge between \"Linz\" and \"Wien\" in a graph with vertices " + strGraph +
                    " returned null.");
            assertNotNull(map.insertEdge("Graz", "Wien", 10), ".insertEdge(): inserting a not existing edge between \"Graz\" and \"Wien\" in a graph with vertices " + strGraph + " " +
                    "returned null.");
            assertNotNull(map.insertEdge("Linz", "Graz", 1), ".insertEdge(): inserting a not existing edge between \"Linz\" and \"Graz\" in a graph with vertices " + strGraph + " " +
                    "returned null.");

        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertExistingEdge() {
        try {
            V linz = map.insertVertex("Linz");
            V wien = map.insertVertex("Wien");
            V graz = map.insertVertex("Graz");
            String strGraph = "[\"Linz\",\"Wien\",\"Graz\"]";

            assertNotNull(map.insertEdge(linz, wien, 100), ".insertEdge(): inserting a not existing edge between \"Linz\" and \"Wien\" in a graph with vertices " + strGraph + " " +
                    "returned null.");
            assertNotNull(map.insertEdge(graz, wien, 10), ".insertEdge(): inserting a not existing edge between \"Graz\" and \"Wien\" in a graph with vertices " + strGraph + " " +
                    "returned null.");
            assertNotNull(map.insertEdge(linz, graz, 1), ".insertEdge(): inserting a not existing edge between \"Linz\" and \"Graz\" in a graph with vertices " + strGraph + " " +
                    "returned null.");

            assertNull(map.insertEdge(linz, graz, 2), ".insertEdge(): inserting an already existing edge between \"Linz\" and \"Graz\" in a graph with vertices " + strGraph + " " +
                    "returned true.");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertEdgeBetweenNotExistingVertex() {
        try {
            V linz = map.insertVertex("Linz");

            assertNull(map.insertEdge("Linz", "Hupfingatsch", 100),
                    ".insertEdge(): inserting an edge in a graph with a single vertex returned not null.");
            assertNull(map.insertEdge("Hupfingatsch", "Linz", 10),
                    ".insertEdge(): inserting an edge in a graph with a single vertex returned not null.");
            assertNull(map.insertEdge("Hupfingatsch", "Christkindl", 1),
                    ".insertEdge(): inserting an edge in a graph with a single vertex returned not null.");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testGetEdges() {
        try {
            V linz = map.insertVertex("Linz");
            V wien = map.insertVertex("Wien");
            V graz = map.insertVertex("Graz");
            String strGraph = "[\"Linz\",\"Wien\",\"Graz\"]";

            map.insertEdge(linz, wien, 100);
            E[] test = map.getEdges();
            assertEquals(1, test.length, ".getEdges() returns array with wrong size for the graph " + strGraph + " and 1 inserted edge.");

            // as we have an undirected graph, we also have to test for a possible edge in opposite direction
            assertTrue((wien == test[0].first && linz == test[0].second) || (wien == test[0].second && linz == test[0].first), ".getEdges(): Did not find correct edge at index 0" +
                    " after inserting the first edge (\"Wien\",\"Linz\",100) in the graph " + strGraph + ".");
            assertEquals(100, test[0].weight, ".getEdges(): The first inserted edge (\"Wien\",\"Linz\",100) in the graph " + strGraph + " has wrong weight: ");

            map.insertEdge(wien, graz, 50);
            test = map.getEdges();
            assertEquals(2, test.length, ".getEdges() returns array with wrong size for the graph " + strGraph + " and 2 inserted edges.");

            // as we have an undirected graph, we also have to test for a possible edge in opposite direction
            assertTrue((wien == test[0].first && linz == test[0].second) || (wien == test[0].second && linz == test[0].first), ".getEdges(): Did not find correct edge at index 0" +
                    " after inserting the first edge (\"Wien\",\"Linz\",100) in the graph " + strGraph + ".");
            assertEquals(100, test[0].weight, ".getEdges(): The first inserted edge (\"Wien\",\"Linz\",100) in the graph " + strGraph + " has wrong weight: ");

            assertTrue((graz == test[1].first && wien == test[1].second) || (graz == test[1].second && wien == test[1].first), ".getEdges(): Did not find correct edge at index 1" +
                    " after inserting the 2nd edge (\"Wien\",\"Graz\",50) in the graph " + strGraph + ".");
            assertEquals(50, test[1].weight, ".getEdges(): The 2nd inserted edge (\"Wien\",\"Graz\",50) in the graph " + strGraph + " has wrong weight: ");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testGetVerticesLarge() {
        try {
            map = initializeLargeGraph();
            String strGraph = "[\"Linz\",\"St.Poelten\",\"Wien\",\"Innsbruck\",\"Bregenz\",\"Eisenstadt\",\"Graz\",\"Klagenfurt\",\"Salzburg\",\"A\",\"B\",\"C\",\"D\",\"E\",\"F\",\"G\",\"H\",\"I\"]";

            V[] v = map.getVertices();
            assertEquals(18, v.length, ".getVertices() returned array of wrong size for the graph with 18 vertices " + strGraph);

            assertEquals("Linz", v[0].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Linz\" should be at index 0.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("St.Poelten", v[1].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"St.Poelten\" should be at index 1.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Wien", v[2].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Wien\" should be at index 2.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Innsbruck", v[3].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Innsbruck\" should be at index 3.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Bregenz", v[4].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Bregenz\" should be at index 4.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Eisenstadt", v[5].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Eisenstadt\" should be at index 5.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Graz", v[6].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Graz\" should be at index 6.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Klagenfurt", v[7].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Klagenfurt\" should be at index 7.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("Salzburg", v[8].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"Salzburg\" should be at index 8.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("A", v[9].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"A\" should be at index 9.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("B", v[10].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"B\" should be at index 10.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("C", v[11].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"C\" should be at index 11.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("D", v[12].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"D\" should be at index 12.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("E", v[13].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"E\" should be at index 13.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("F", v[14].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"F\" should be at index 14.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("G", v[15].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"G\" should be at index 15.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("H", v[16].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"H\" should be at index 16.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
            assertEquals("I", v[17].toString(), ".getVertices(): For the graph with the vertices " + strGraph + " the vertex \"I\" should be at index 17.\n"
                    + "\tYour vertices array is: " + printVerticesArray());
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHasEdgeForUndirectedGraph() {
        try {
            map = initializeLargeGraph();

            String strEdges = "(v1,v2,weight) [(0,2,1),(2,5,2),(2,6,3),(6,7,4),(4,3,5),(7,3,6),(8,3,7),(8,10,8),(7,11,9),(1,9,10),(10,9,11),(13,14,12),(14,15,13),(15,16,14),(16,12,15),(16,17,16)]";

            assertEquals(1, map.findEdge(map.vertices[0], map.vertices[2]).weight,
                    ".findEdge() returned a wrong weight for the edge (0,2) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);

            assertEquals(2, map.findEdge(map.vertices[2], map.vertices[5]).weight,
                    ".findEdge() returned a wrong weight for the edge (2,5) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(3, map.findEdge(map.vertices[2], map.vertices[6]).weight,
                    ".findEdge() returned a wrong weight for the edge (2,6) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(4, map.findEdge(map.vertices[6], map.vertices[7]).weight,
                    ".findEdge() returned a wrong weight for the edge (6,7) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(5, map.findEdge(map.vertices[4], map.vertices[3]).weight,
                    ".findEdge() returned a wrong weight for the edge (4,3) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(7, map.findEdge(map.vertices[8], map.vertices[3]).weight,
                    ".findEdge() returned a wrong weight for the edge (8,3) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(8, map.findEdge(map.vertices[8], map.vertices[10]).weight,
                    ".findEdge() returned a wrong weight for the edge (8,10) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(11, map.findEdge(map.vertices[10], map.vertices[9]).weight,
                    ".findEdge() returned a wrong weight for the edge (10,9) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(9, map.findEdge(map.vertices[7], map.vertices[11]).weight,
                    ".findEdge() returned a wrong weight for the edge (7,11) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(15, map.findEdge(map.vertices[16], map.vertices[12]).weight,
                    ".findEdge() returned a wrong weight for the edge (16,12) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);

        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHasEdgeForUndirectedGraphWithOpposites() {
        try {
            map = initializeLargeGraph();

            String strEdges = "(v1,v2,weight) [(0,2,1),(2,5,2),(2,6,3),(6,7,4),(4,3,5),(7,3,6),(8,3,7),(8,10,8),(7,11,9),(1,9,10),(10,9,11),(13,14,12),(14,15,13),(15,16,14),(16,12,15),(16,17,16)]";

            assertEquals(1, map.findEdge(map.vertices[2], map.vertices[0]).weight,
                    ".findEdge() returned a wrong weight for the edge (2,0) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);

            assertEquals(2, map.findEdge(map.vertices[5], map.vertices[2]).weight, ".findEdge() returned a wrong weight for the edge (5,2) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);
            assertEquals(3, map.findEdge(map.vertices[6], map.vertices[2]).weight, ".findEdge() returned a wrong weight for the edge (6,2) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);
            assertEquals(4, map.findEdge(map.vertices[7], map.vertices[6]).weight, ".findEdge() returned a wrong weight for the edge (7,6) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);
            assertEquals(5, map.findEdge(map.vertices[3], map.vertices[4]).weight, ".findEdge() returned a wrong weight for the edge (3,4) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);
            assertEquals(7, map.findEdge(map.vertices[3], map.vertices[8]).weight, ".findEdge() returned a wrong weight for the edge (3,8) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);
            assertEquals(8, map.findEdge(map.vertices[10], map.vertices[8]).weight,
                    ".findEdge() returned a wrong weight for the edge (10,8) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(11, map.findEdge(map.vertices[9], map.vertices[10]).weight,
                    ".findEdge() returned a wrong weight for the edge (9,10) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(9, map.findEdge(map.vertices[11], map.vertices[7]).weight,
                    ".findEdge() returned a wrong weight for the edge (11,7) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);
            assertEquals(15, map.findEdge(map.vertices[12], map.vertices[16]).weight,
                    ".findEdge() returned a wrong weight for the edge (12,16) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);

        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testHasEdgeForUndirectedGraphWithNotExistingEdges() {
        try {
            map = initializeLargeGraph();

            String strEdges = "(v1,v2,weight) [(0,2,1),(2,5,2),(2,6,3),(6,7,4),(4,3,5),(7,3,6),(8,3,7),(8,10,8),(7,11,9),(1,9,10),(10,9,11),(13,14,12),(14,15,13),(15,16,14),(16,12,15),(16,17,16)]";

            assertNull(map.findEdge(map.vertices[2], map.vertices[10]),
                    ".findEdge() returned not null for the not existing edge (2,10) \n\t of the graph " + printVerticesArray() +
                            "\n\t with the edges " + strEdges);

            assertNull(map.findEdge(map.vertices[5], map.vertices[0]), ".findEdge" +
                    "() returned not null for the not existing edge (5,0) \n\t of the graph " + printVerticesArray() +
                    "\n\t with the edges " + strEdges);


        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    int[][] expectedMatrix_undirectedGraph = {
            {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
            {1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
            {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1},
            {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0}
    };

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testGetAdjacencyMatrix() {
        try {
            map = initializeLargeGraph();
            String strEdges = "(v1,v2,weight) [(0,2,1),(2,5,2),(2,6,3),(6,7,4),(4,3,5),(7,3,6),(8,3,7),(8,10,8),(7,11,9),(1,9,10),(10,9,11),(13,14,12),(14,15,13),(15,16,14),(16,12,15),(16,17,16)]";

            int[][] expectedMatrix = expectedMatrix_undirectedGraph;

            int[][] matrix = map.getAdjacencyMatrix();

            //expected result for directed graphs:
            // 0	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	1	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	1	1	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	1	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	1	0	0	0	0	0	0	0	1	0	0	0	0	0	0
            // 0	0	0	1	0	0	0	0	0	0	1	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	1	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	1	0	0	0	0	1
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0

            //expected result for undirected graphs:
            // 0	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	1	0	0	0	0	0	0	0	0
            // 1	0	0	0	0	1	1	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	1	0	0	1	1	0	0	0	0	0	0	0	0	0
            // 0	0	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	1	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0
            // 0	0	1	0	0	0	0	1	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	1	0	0	1	0	0	0	0	1	0	0	0	0	0	0
            // 0	0	0	1	0	0	0	0	0	0	1	0	0	0	0	0	0	0
            // 0	1	0	0	0	0	0	0	0	0	1	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	1	1	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	1	0	0	0	0	0	0	0	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	1	0	1	0	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0	1	0
            // 0	0	0	0	0	0	0	0	0	0	0	0	1	0	0	1	0	1
            // 0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	0	1	0

            StringBuilder sb = new StringBuilder();

            for (int i = 0; i < expectedMatrix.length; i++) {
                for (int j = 0; j < expectedMatrix.length; j++) {
                    if (expectedMatrix[i][j] == 0 && matrix[i][j] != -1) {
                        sb.append("\t-> Error (no edge weight should be set) @ matrix position: [").append(i).append(",").append(j).append("]\n");
                    }
                    if (expectedMatrix[i][j] == 1 && matrix[i][j] <= 0) {
                        sb.append("\t-> Error (edge weight should be set) @ matrix position: [").append(i).append(",").append(j).append("]\n");
                    }
                }
            }

            assertEquals(0, sb.length(), ".getAdjacencyMatrix() failed \n\tfor the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges +
                    "\n\tat the following positions:\n" + sb);
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testNumAdjacentVerticesOfUndirectedGraph() {
        try {
            map = initializeLargeGraph();
            String strEdges = "(v1,v2,weight) [(0,2,1),(2,5,2),(2,6,3),(6,7,4),(4,3,5),(7,3,6),(8,3,7),(8,10,8),(7,11,9),(1,9,10),(10,9,11),(13,14,12),(14,15,13),(15,16,14),(16,12,15),(16,17,16)]";

            V[] v0 = map.getAdjacentVertices(map.vertices[0]);
            assertEquals(1, v0.length, ".getAdjacentVertices() failed for vertex with index 0 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");

            V[] v1 = map.getAdjacentVertices(map.vertices[1]);
            assertEquals(1, v1.length, ".getAdjacentVertices() failed for vertex with index 1 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v2 = map.getAdjacentVertices(map.vertices[2]);
            assertEquals(3, v2.length, ".getAdjacentVertices() failed for vertex with index 2 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v3 = map.getAdjacentVertices(map.vertices[3]);
            assertEquals(3, v3.length, ".getAdjacentVertices() failed for vertex with index 3 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v4 = map.getAdjacentVertices(map.vertices[4]);
            assertEquals(1, v4.length, ".getAdjacentVertices() failed for vertex with index 4 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v5 = map.getAdjacentVertices(map.vertices[5]);
            assertEquals(1, v5.length, ".getAdjacentVertices() failed for vertex with index 5 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v6 = map.getAdjacentVertices(map.vertices[6]);
            assertEquals(2, v6.length, ".getAdjacentVertices() failed for vertex with index 6 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v7 = map.getAdjacentVertices(map.vertices[7]);
            assertEquals(3, v7.length, ".getAdjacentVertices() failed for vertex with index 7 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v8 = map.getAdjacentVertices(map.vertices[8]);
            assertEquals(2, v8.length, ".getAdjacentVertices() failed for vertex with index 8 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");

            V[] v9 = map.getAdjacentVertices(map.vertices[9]);
            assertEquals(2, v9.length, ".getAdjacentVertices() failed for vertex with index 9 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v10 = map.getAdjacentVertices(map.vertices[10]);
            assertEquals(2, v10.length, ".getAdjacentVertices() failed for vertex with index 10 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v11 = map.getAdjacentVertices(map.vertices[11]);
            assertEquals(1, v11.length, ".getAdjacentVertices() failed for vertex with index 11 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v12 = map.getAdjacentVertices(map.vertices[12]);
            assertEquals(1, v12.length, ".getAdjacentVertices() failed for vertex with index 12 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v13 = map.getAdjacentVertices(map.vertices[13]);
            assertEquals(1, v13.length, ".getAdjacentVertices() failed for vertex with index 13 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v14 = map.getAdjacentVertices(map.vertices[14]);
            assertEquals(2, v14.length, ".getAdjacentVertices() failed for vertex with index 14 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v15 = map.getAdjacentVertices(map.vertices[15]);
            assertEquals(2, v15.length, ".getAdjacentVertices() failed for vertex with index 15 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v16 = map.getAdjacentVertices(map.vertices[16]);
            assertEquals(3, v16.length, ".getAdjacentVertices() failed for vertex with index 16 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            V[] v17 = map.getAdjacentVertices(map.vertices[17]);
            assertEquals(1, v17.length, ".getAdjacentVertices() failed for vertex with index 17 " +
                    "\n\tof the graph " + printVerticesArray() +
                    "\n\twith the edges " + strEdges + "\n\n\t");
            assertNull(map.getAdjacentVertices("Hupfingatsch"),
                    ".getAdjacentVertices() did not return null for unknown vertex");
        } catch (Exception ex) {
            fail("Could not test as an exception has been thrown: " + ex);
        }
    }

    // IllegalArgumentException tests

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertVertexNullParameter() {
        assertThrows(IllegalArgumentException.class, () -> {
                    V linz = map.insertVertex(null);
                },
                ".insertVertex() did not throw an IllegalArgumentException in case of passing null.");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFindVertexNullParameter() {
        assertThrows(IllegalArgumentException.class, () -> {
                    V linz = map.findVertex(null);
                },
                ".findVertex() did not throw an IllegalArgumentException in case of passing null.");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertEdgeNullParameter() {
        V linz = map.insertVertex("Linz");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge(linz, null, 1);
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge(null, linz, 1);
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge("Linz", null, 1);
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge(null, "Linz", 1);
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of passing null.");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testFindEdgeNullParameter() {
        V linz = map.insertVertex("Linz");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.findEdge(linz, null);
                },
                ".findEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.findEdge(null, linz);
                },
                ".findEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.findEdge("Linz", null);
                },
                ".findEdge() did not throw an IllegalArgumentException in case of passing null.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.findEdge(null, "Linz");
                },
                ".findEdge() did not throw an IllegalArgumentException in case of passing null.");
    }

    @Test
    @Timeout(value = 500, unit = TimeUnit.MILLISECONDS)
    public void testInsertEdgeLoop() {
        V linz = map.insertVertex("Linz");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge(linz, linz, (int) (Math.random() * 100));
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of inserting a loop.");
        assertThrows(IllegalArgumentException.class, () -> {
                    map.insertEdge("Linz", "Linz", (int) (Math.random() * 100));
                },
                ".insertEdge() did not throw an IllegalArgumentException in case of inserting a loop.");
    }

    //--------------------------------------
    //--- PRIVATE Methods
    private static G initializeLargeGraph() {
        G map = new G();

        V linz = map.insertVertex("Linz");               // 0
        V stpoelten = map.insertVertex("St.Poelten");    // 1
        V wien = map.insertVertex("Wien");               // 2
        V innsbruck = map.insertVertex("Innsbruck");     // 3
        V bregenz = map.insertVertex("Bregenz");         // 4
        V eisenstadt = map.insertVertex("Eisenstadt");   // 5
        V graz = map.insertVertex("Graz");               // 6
        V klagenfurt = map.insertVertex("Klagenfurt");   // 7
        V salzburg = map.insertVertex("Salzburg");       // 8

        map.insertEdge(linz.name, wien.name, 1);                // (0,2,1)
        map.insertEdge(wien.name, eisenstadt.name, 2);        // (2,5,2)
        map.insertEdge(wien.name, graz.name, 3);                // (2,6,3)
        map.insertEdge(graz.name, klagenfurt.name, 4);        // (6,7,4)
        map.insertEdge(bregenz.name, innsbruck.name, 5);        // (4,3,5)
        map.insertEdge(klagenfurt.name, innsbruck.name, 6);    // (7,3,6)
        map.insertEdge(salzburg.name, innsbruck.name, 7);        // (8,3,7)

        V a = map.insertVertex("A");    // 9
        V b = map.insertVertex("B");    // 10
        V c = map.insertVertex("C");    // 11
        V d = map.insertVertex("D");    // 12
        V e = map.insertVertex("E");    // 13
        V f = map.insertVertex("F");    // 14
        V g = map.insertVertex("G");    // 15
        V h = map.insertVertex("H");    // 16
        V i = map.insertVertex("I");    // 17

        map.insertEdge(salzburg.name, b.name, 8);        // (8,10,8)
        map.insertEdge(klagenfurt.name, c.name, 9);    // (7,11,9)
        map.insertEdge(stpoelten.name, a.name, 10);    // (1,9,10)
        map.insertEdge(b.name, a.name, 11);            // (10,9,11)

        map.insertEdge(e.name, f.name, 12);            // (13,14,12)
        map.insertEdge(f.name, g.name, 13);            // (14,15,13)
        map.insertEdge(g.name, h.name, 14);            // (15,16,14)
        map.insertEdge(h.name, d.name, 15);            // (16,12,15)
        map.insertEdge(h.name, i.name, 16);            // (16,17,16)

        return map;
    }

    private String printVerticesArray() {
        StringBuilder sb = new StringBuilder();
        V[] v = map.getVertices();

        sb.append("[");
        for (int i = 0; i < v.length; i++) {
            sb.append(i).append("=\"").append(v[i].toString()).append("\",");
        }
        sb.replace(sb.length() - 1, sb.length(), "]");

        return sb.toString();
    }
}
