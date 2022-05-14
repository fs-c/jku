package assignment03;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;

public class MazeTest {
	private class MazeSolveStruct{
		char [][] maze;
		char [][] mazeSolved;
		ArrayList<int[]> listOfExits;
		int startRow;
		int startCol;
		int maxRecDepth;

		MazeSolveStruct(){
			maze = null;
			mazeSolved = null;
			listOfExits = new ArrayList<int[]>();
			startRow = 0;
			startCol = 0;
			maxRecDepth = 0;
		}
	}

	/**************************************************************************************************************
	 * ************************************
	 * 	 *
	 * ************************************
	 *************************************************************************************************************/

	@Test
	public void TestOneExit() {
		MazeSolveStruct myMazeStruct = createMaze(0);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
		assertTrue(retval, "Test with 1 exit: No exit found!");

		// check found exit
		checkExits("Test with 1 exit failed: ",myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestTwoExits() {
		MazeSolveStruct myMazeStruct = createMaze(3);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
		assertTrue(retval, "Test with 2 exits failed: No exit found!");

		// check found exits
		checkExits("Test with 2 exits failed: Exits found @: "+printListOfExits(maze.getListOfExits()),myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestMinMazeWithExit() {
		MazeSolveStruct myMazeStruct = createMaze(1);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
		assertTrue(retval, "Test minimal maze with one exit: No exit found!");

		// check found exits
		checkExits("Test minimal maze with one exit failed: ",myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestSplitMazeWithTwoExits() {
		MazeSolveStruct myMazeStruct = createMaze(5);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

		assertTrue(retval, "Test split maze with two exits: No exit found!");

		// check found exits
		checkExits("Test split maze with two exits: ",myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestSplitMazeWithoutExit() {
		MazeSolveStruct myMazeStruct = createMaze(2);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

		assertFalse(retval, "Test maze without exit failed: "+maze.getListOfExits().size()+" exit(s) found!\n"
				+printMaze(maze.getMaze()));
	}

	@Test
	public void TestBigMazeOneExit() {
		MazeSolveStruct myMazeStruct = createMaze(7);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
		//maze.dumpMaze();
		assertTrue(retval, "Test big maze: No exit found!");

		// check found exits
		checkExits("Test big maze with one exit failed: ",myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestMinMazeWithFourExits() {
		MazeSolveStruct myMazeStruct = createMaze(4);
		assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

		// analyse maze
		boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
		assertTrue(retval, "Minimal maze with four exits: No exit found!");

		// check found exits
		checkExits("Minimal maze with four exits failed: ",myMazeStruct.listOfExits, maze.getListOfExits(), maze.getMaze());
	}

	@Test
	public void TestInvalidMaze1() {
		Exception temp = null;
		try {
			assignment03.Maze maze = new assignment03.Maze(null);
		} catch (Exception ex) {
			temp = ex;
		}
		assertTrue(temp instanceof IllegalArgumentException, "Invalid maze constructed with null instead of a char[][] didn't throw an IllegalArgumentException!");
	}

	@Test
	public void TestInvalidMazeNotSquare() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(9);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);
		} catch (Exception ex) {
			assertTrue(ex instanceof IllegalArgumentException, "Invalid maze constructed with a non-square char[][] didn't throw and IllegalArgumentException!");
		}
	}

	@Test
	public void TestMinMazeWithoutExit() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(2);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

			assertFalse(retval, "Exit found ("+printListOfExits(maze.getListOfExits())
					+")where none should be!\n"+printMaze(maze.getMaze()));

			// check found exit
			ArrayList<int[]> listOfExits = maze.getListOfExits();
			assertEquals(myMazeStruct.listOfExits.size(), listOfExits.size(), "Exit found ("+printListOfExits(maze.getListOfExits())
					+")where none should be!\n"
					+printMaze(maze.getMaze()));
		} catch (Exception ex) {
			assertTrue(ex instanceof IllegalArgumentException, ex.getClass()+" thrown where it shouldn't!");
		}
	}

	@Test
	public void TestMaxRecDepth1() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(2);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

			// check max recursion depth
			assertTrue(maze.getMaxRecursionDepth() <= myMazeStruct.maxRecDepth, "Test (1) max. recursion depth failed. Your depth ("+maze.getMaxRecursionDepth()
					+")is greater than max. depth ("+myMazeStruct.maxRecDepth+") for the maze:\n"
					+printMaze(maze.getMaze()));
		} catch (Exception ex) {
			assertNull(ex, "Test (1) max. recursion depth failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestMaxRecDepth2() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(7);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
			//System.out.println("Max rec depth: "+maze.getMaxRecursionDepth());
			// check max recursion depth
			assertTrue(maze.getMaxRecursionDepth() <= myMazeStruct.maxRecDepth, "Test (2) max. recursion depth failed. Your depth ("+maze.getMaxRecursionDepth()
					+")is greater than max. depth ("+myMazeStruct.maxRecDepth+") for the maze:\n"
					+printMaze(maze.getMaze()));
		} catch (Exception ex) {
			assertNull(ex, "Test (2) max. recursion depth failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestMaxRecDepth3() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(10);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
			//System.out.println("Max rec depth: "+maze.getMaxRecursionDepth());
			// check max recursion depth
			assertTrue(maze.getMaxRecursionDepth() <= myMazeStruct.maxRecDepth, "Test (3) max. recursion depth failed. Your depth ("+maze.getMaxRecursionDepth()
					+")is greater than max. depth ("+myMazeStruct.maxRecDepth+") for the maze:\n"
					+printMaze(maze.getMaze()));
		} catch (Exception ex) {
			assertNull(ex, "Test (3) max. recursion depth failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestDiagonalMovementWithoutExit() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(8);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);
			assertFalse(retval, "Exit found ("+printListOfExits(maze.getListOfExits())
					+")where none should be!\n"+printMaze(maze.getMaze()));

			// check found exit
			ArrayList<int[]> listOfExits = maze.getListOfExits();
			assertEquals(myMazeStruct.listOfExits.size(), listOfExits.size(), "Exit found ("+printListOfExits(maze.getListOfExits())
					+")where none should be!\n"
					+printMaze(maze.getMaze()));
		} catch (Exception ex) {
			assertNull(ex, "Test (2) max. recursion depth failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestMazeMapOneExit() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(7);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

			for(int row = 0; row < myMazeStruct.mazeSolved.length; row++) {
				for (int col = 0; col < myMazeStruct.mazeSolved[row].length; col++) {
					assertEquals(myMazeStruct.mazeSolved[row][col], maze.getMaze()[row][col], "Test of maze map (1 exit): Wrong char found at position [row="+row+",col="+col+"] - expected '"
							+myMazeStruct.mazeSolved[row][col]+"' but found '"+maze.getMaze()[row][col]+"'\n"
							+printMaze(maze.getMaze()) );
				}

			}
		} catch (Exception ex) {
			assertNull(ex, "Test maze map (1 exit) failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestMazeMapMultipleExits() {
		try {
			MazeSolveStruct myMazeStruct = createMaze(11);
			assignment03.Maze maze = new assignment03.Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

			for(int row = 0; row < myMazeStruct.mazeSolved.length; row++) {
				for (int col = 0; col < myMazeStruct.mazeSolved[row].length; col++) {
					assertEquals(myMazeStruct.mazeSolved[row][col], maze.getMaze()[row][col], "Test of maze map (multiple exits): Wrong char found at position [row="+row+", col"+col+"] - expected '"
							+myMazeStruct.mazeSolved[row][col]+"' but found '"+maze.getMaze()[row][col]+"'\n"
							+printMaze(maze.getMaze()) );
				}

			}
		} catch (Exception ex) {
			assertNull(ex, "Test maze map (multiple exits) failed as exception was thrown: "+ex.getClass());
		}
	}

	@Test
	public void TestMazeMapDiagonal() {	// diagonal
		try {
			MazeSolveStruct myMazeStruct = createMaze(8);
			assignment03.Maze maze = new Maze(myMazeStruct.maze);	// generate maze object

			// analyse maze
			boolean retval = maze.locateExits(myMazeStruct.startRow, myMazeStruct.startCol, 0);

			for(int row = 0; row < myMazeStruct.mazeSolved.length; row++) {
				for (int col = 0; col < myMazeStruct.mazeSolved[row].length; col++) {
					assertEquals(myMazeStruct.mazeSolved[row][col], maze.getMaze()[row][col], "Test of maze map (diagonal): Wrong char found at position [row="+row+",col="+col+"] - expected '"
							+myMazeStruct.mazeSolved[row][col]+"' but found '"+maze.getMaze()[row][col]+"'\n"
							+printMaze(maze.getMaze()));
				}

			}
		} catch (Exception ex) {
			assertNull(ex, "Test maze map (diagonal) failed as exception was thrown: "+ex.getClass());
		}
	}

	/**************************************************************************************/


	// This auxiliary method helps to create different mazes, depending on the given maze_type.
	private MazeSolveStruct createMaze(final int mazeType) {
		MazeSolveStruct myMazeStruct = new MazeSolveStruct();

		//char [][] maze = null;

		switch(mazeType) {
			case 0:

				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "******".toCharArray();
				myMazeStruct.maze[1]  = "*    *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  * *".toCharArray();
				myMazeStruct.maze[4]  = "* ** *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();


				myMazeStruct.listOfExits.add(new int[] {5,4});
				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "******".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*S...*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "**.*.*".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*..*.*".toCharArray();
				myMazeStruct.mazeSolved[4]  = "*.**.*".toCharArray();
				myMazeStruct.mazeSolved[5]  = "****X*".toCharArray();
				break;

			case 1:
				myMazeStruct.maze = new char[3][3];
				myMazeStruct.maze[0]  = "***".toCharArray();
				myMazeStruct.maze[1]  = "  *".toCharArray();
				myMazeStruct.maze[2]  = "***".toCharArray();

				myMazeStruct.listOfExits.add(new int[] {1,0});
				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;
				myMazeStruct.maxRecDepth = 1;

				myMazeStruct.mazeSolved = new char[3][3];
				myMazeStruct.mazeSolved[0]  = "***".toCharArray();
				myMazeStruct.mazeSolved[1]  = ".S*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "***".toCharArray();
				break;

			case 2:
				myMazeStruct.maze = new char[3][3];
				myMazeStruct.maze[0]  = "***".toCharArray();
				myMazeStruct.maze[1]  = "* *".toCharArray();
				myMazeStruct.maze[2]  = "***".toCharArray();

				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;
				myMazeStruct.maxRecDepth = 1;

				myMazeStruct.mazeSolved = new char[3][3];
				myMazeStruct.mazeSolved[0]  = "***".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*S*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "***".toCharArray();
				break;

			case 3:
				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "******".toCharArray();
				myMazeStruct.maze[1]  = "*    *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  *  ".toCharArray();
				myMazeStruct.maze[4]  = "* ** *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();


				myMazeStruct.listOfExits.add(new int[] {5,4});
				myMazeStruct.listOfExits.add(new int[] {3,5});
				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "******".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*S...*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "**.*.*".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*..*.X".toCharArray();
				myMazeStruct.mazeSolved[4]  = "*.**.*".toCharArray();
				myMazeStruct.mazeSolved[5]  = "****X*".toCharArray();
				break;


			case 4:
				myMazeStruct.maze = new char[3][3];
				myMazeStruct.maze[0]  = "* *".toCharArray();
				myMazeStruct.maze[1]  = "   ".toCharArray();
				myMazeStruct.maze[2]  = "* *".toCharArray();

				myMazeStruct.listOfExits.add(new int[] {0,1});
				myMazeStruct.listOfExits.add(new int[] {1,0});
				myMazeStruct.listOfExits.add(new int[] {2,1});
				myMazeStruct.listOfExits.add(new int[] {1,2});
				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;

				myMazeStruct.mazeSolved = new char[3][3];
				myMazeStruct.mazeSolved[0]  = "*X*".toCharArray();
				myMazeStruct.mazeSolved[1]  = "XSX".toCharArray();
				myMazeStruct.mazeSolved[2]  = "*X*".toCharArray();
				break;

			case 5:
				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "******".toCharArray();
				myMazeStruct.maze[1]  = "*  * *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  *  ".toCharArray();
				myMazeStruct.maze[4]  = "* ** *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();

				myMazeStruct.listOfExits.add(new int[] {3,5});
				myMazeStruct.listOfExits.add(new int[] {5,4});
				myMazeStruct.startRow = 4;
				myMazeStruct.startCol = 4;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "******".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*  *.*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "** *.*".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*  *.X".toCharArray();
				myMazeStruct.mazeSolved[4]  = "* **S*".toCharArray();
				myMazeStruct.mazeSolved[5]  = "****X*".toCharArray();
				break;

			case 6:
				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "******".toCharArray();
				myMazeStruct.maze[1]  = "*  * *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  *  ".toCharArray();
				myMazeStruct.maze[4]  = "* ** *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();

				myMazeStruct.startRow = 2;
				myMazeStruct.startCol = 3;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "******".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*..* *".toCharArray();
				myMazeStruct.mazeSolved[2]  = "**.* *".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*.S*  ".toCharArray();
				myMazeStruct.mazeSolved[4]  = "*.** *".toCharArray();
				myMazeStruct.mazeSolved[5]  = "**** *".toCharArray();
				break;

			case 7:
				myMazeStruct.maze = new char[15][15];

				myMazeStruct.maze[0]  = "***************".toCharArray();
				myMazeStruct.maze[1]  = "*      *      *".toCharArray(); // 12
				myMazeStruct.maze[2]  = "*** * ******  *".toCharArray(); //  4
				myMazeStruct.maze[3]  = "*   * ******* *".toCharArray(); //  5
				myMazeStruct.maze[4]  = "* ***         *".toCharArray(); // 10
				myMazeStruct.maze[5]  = "*   *******   *".toCharArray(); //  6
				myMazeStruct.maze[6]  = "*** *         *".toCharArray(); // 10
				myMazeStruct.maze[7]  = "    * ******  *".toCharArray(); //  6
				myMazeStruct.maze[8]  = "*****      ** *".toCharArray(); //  7
				myMazeStruct.maze[9]  = "***** ******  *".toCharArray(); //  3
				myMazeStruct.maze[10] = "*         **  *".toCharArray(); // 11
				myMazeStruct.maze[11] = "* ********** **".toCharArray(); //  2
				myMazeStruct.maze[12] = "*          * **".toCharArray(); // 11
				myMazeStruct.maze[13] = "*   **       **".toCharArray(); // 10
				myMazeStruct.maze[14] = "***************".toCharArray(); // --
				// 97 = max. rec. depth
				myMazeStruct.listOfExits.add(new int[] {7,0});

				myMazeStruct.startRow = 13;
				myMazeStruct.startCol = 9;
				myMazeStruct.maxRecDepth = 97;

				myMazeStruct.mazeSolved = new char[15][15];
				myMazeStruct.mazeSolved[0]  = "***************".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*......*......*".toCharArray(); // 12
				myMazeStruct.mazeSolved[2]  = "***.*.******..*".toCharArray(); //  4
				myMazeStruct.mazeSolved[3]  = "*...*.*******.*".toCharArray(); //  5
				myMazeStruct.mazeSolved[4]  = "*.***.........*".toCharArray(); // 10
				myMazeStruct.mazeSolved[5]  = "*...*******...*".toCharArray(); //  6
				myMazeStruct.mazeSolved[6]  = "***.*.........*".toCharArray(); // 10
				myMazeStruct.mazeSolved[7]  = "X...*.******..*".toCharArray(); //  6
				myMazeStruct.mazeSolved[8]  = "*****......**.*".toCharArray(); //  7
				myMazeStruct.mazeSolved[9]  = "*****.******..*".toCharArray(); //  3
				myMazeStruct.mazeSolved[10] = "*.........**..*".toCharArray(); // 11
				myMazeStruct.mazeSolved[11] = "*.**********.**".toCharArray(); //  2
				myMazeStruct.mazeSolved[12] = "*..........*.**".toCharArray(); // 11
				myMazeStruct.mazeSolved[13] = "*...**...S...**".toCharArray(); // 10
				myMazeStruct.mazeSolved[14] = "***************".toCharArray();
				break;

			case 8:	// diagonal movement
				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "******".toCharArray();
				myMazeStruct.maze[1]  = "*  * *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  *  ".toCharArray();
				myMazeStruct.maze[4]  = "* *  *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();

				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "******".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*S.* *".toCharArray();
				myMazeStruct.mazeSolved[2]  = "**.* *".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*..*  ".toCharArray();
				myMazeStruct.mazeSolved[4]  = "*.*  *".toCharArray();
				myMazeStruct.mazeSolved[5]  = "**** *".toCharArray();
				break;

			case 9:
				// invalid maze as it is not square
				myMazeStruct.maze = new char[3][4];
				myMazeStruct.maze[0]  = "****".toCharArray();
				myMazeStruct.maze[1]  = "*  *".toCharArray();
				myMazeStruct.maze[2]  = "****".toCharArray();

				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;
				myMazeStruct.maxRecDepth = 1;
				break;

			case 10:
				myMazeStruct.maze = new char[15][15];

				myMazeStruct.maze[0]  = "***************".toCharArray();
				myMazeStruct.maze[1]  = "*             *".toCharArray(); // 13
				myMazeStruct.maze[2]  = "************* *".toCharArray(); //  1
				myMazeStruct.maze[3]  = "*             *".toCharArray(); // 13
				myMazeStruct.maze[4]  = "* *************".toCharArray(); //  1
				myMazeStruct.maze[5]  = "*             *".toCharArray(); // 13
				myMazeStruct.maze[6]  = "************* *".toCharArray(); //  1
				myMazeStruct.maze[7]  = "*             *".toCharArray(); // 13
				myMazeStruct.maze[8]  = "* *************".toCharArray(); //  1
				myMazeStruct.maze[9]  = "*             *".toCharArray(); // 13
				myMazeStruct.maze[10] = "************* *".toCharArray(); //  1
				myMazeStruct.maze[11] = "************* *".toCharArray(); //  1
				myMazeStruct.maze[12] = "************* *".toCharArray(); //  1
				myMazeStruct.maze[13] = "*             *".toCharArray(); // 13
				myMazeStruct.maze[14] = "***************".toCharArray(); // --
				// 85 = max. rec. depth

				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;
				myMazeStruct.maxRecDepth = 85;

				myMazeStruct.mazeSolved = new char[15][15];
				myMazeStruct.mazeSolved[0]  = "***************".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[2]  = "************* *".toCharArray(); //  1
				myMazeStruct.mazeSolved[3]  = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[4]  = "* *************".toCharArray(); //  1
				myMazeStruct.mazeSolved[5]  = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[6]  = "************* *".toCharArray(); //  1
				myMazeStruct.mazeSolved[7]  = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[8]  = "* *************".toCharArray(); //  1
				myMazeStruct.mazeSolved[9]  = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[10] = "************* *".toCharArray(); //  1
				myMazeStruct.mazeSolved[11] = "************* *".toCharArray(); //  1
				myMazeStruct.mazeSolved[12] = "************* *".toCharArray(); //  1
				myMazeStruct.mazeSolved[13] = "*             *".toCharArray(); // 13
				myMazeStruct.mazeSolved[14] = "***************".toCharArray(); // --
				break;

			case 11:
				myMazeStruct.maze = new char[6][6];
				myMazeStruct.maze[0]  = "** ***".toCharArray();
				myMazeStruct.maze[1]  = "*    *".toCharArray();
				myMazeStruct.maze[2]  = "** * *".toCharArray();
				myMazeStruct.maze[3]  = "*  *  ".toCharArray();
				myMazeStruct.maze[4]  = "  ** *".toCharArray();
				myMazeStruct.maze[5]  = "**** *".toCharArray();

				myMazeStruct.listOfExits.add(new int[] {0,2});
				myMazeStruct.listOfExits.add(new int[] {3,5});
				myMazeStruct.listOfExits.add(new int[] {4,0});
				myMazeStruct.listOfExits.add(new int[] {5,4});
				myMazeStruct.startRow = 1;
				myMazeStruct.startCol = 1;

				myMazeStruct.mazeSolved = new char[6][6];
				myMazeStruct.mazeSolved[0]  = "**X***".toCharArray();
				myMazeStruct.mazeSolved[1]  = "*S...*".toCharArray();
				myMazeStruct.mazeSolved[2]  = "**.*.*".toCharArray();
				myMazeStruct.mazeSolved[3]  = "*..*.X".toCharArray();
				myMazeStruct.mazeSolved[4]  = "X.**.*".toCharArray();
				myMazeStruct.mazeSolved[5]  = "****X*".toCharArray();
				break;

			default:

				break;
		}
		return myMazeStruct;
	}

	private void checkExits(String errorMsg, ArrayList<int[]> listSolution, ArrayList<int[]> listStudent, char[][] studMaze) {
		assertEquals(listSolution.size(), listStudent.size(), errorMsg+" Wrong number of exits! Exit(s) found @: "+printListOfExits(listStudent)+"\n"+printMaze(studMaze));
		for(int i = 0; i < listSolution.size(); i++) {
			boolean found = false;
			for(int[] studExit : listStudent) {
				if(listSolution.get(i)[0] == studExit[0]) {
					if(listSolution.get(i)[1] == studExit[1]) {
						found = true;
						break;
					}
				}
			}
			assertTrue(found, errorMsg+"Exit @[row="+listSolution.get(i)[0]+",col="+listSolution.get(i)[1]+"] not found!\n"+printMaze(studMaze));
		}
	}


	private String printListOfExits(ArrayList<int[]> list) {
		StringBuilder str = new StringBuilder();

		for (int i = 0; i < list.size(); i++) {
			str.append("[row="+list.get(i)[0]+",col="+list.get(i)[1]+"] ");

		}
		str.append("\n");

		return str.toString();

	}

	private String printMaze(char[][] maze) {
		StringBuilder str = new StringBuilder();

		str.append("\n x 012");
		for(int i = 3; i < maze.length; i++) str.append("-");
		str.append("\n");
		for (int i = 0; i < maze.length; i++) {
			if(i==0) {
				str.append("y\n0  ");
			}
			else if(i == 1) str.append("1  ");
			else if(i == 2) str.append("2  ");
			else str.append("|  ");

			str.append(maze[i]);
			str.append("\n");

		}

		return str.toString();
	}
}
// EOT11
