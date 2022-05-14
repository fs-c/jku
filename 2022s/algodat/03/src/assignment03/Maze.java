package assignment03;

import java.util.ArrayList;

public class Maze implements IMaze {
	private char [][] maze	= null;

	private int maximumRecursionDepth = -1;

	private ArrayList<int[]> exits = new ArrayList<>();

	// default constructor
	public Maze(char[][] maze) {
		if(maze != null) {
			this.maze = maze;
			
		} else throw new IllegalArgumentException();

	}

	private boolean isAtEdge(final int row, final int col) {
		return row == 0 || col == 0 || row == maze.length - 1 || col == maze[0].length - 1;
	}

	private void addExit(final int row, final int col) {
		for (int[] pair : exits) {
			if (pair[0] == row && pair[1] == col) {
				return;
			}
		}

		exits.add(new int[]{ row, col });
	}

	public boolean locateExits(final int row, final int col, int depth) {
		if (depth > maximumRecursionDepth) {
			maximumRecursionDepth = depth;
		}

		if (row >= maze.length || col >= maze[0].length) {
			throw new IllegalArgumentException("starting position out of bounds");
		}

		if (depth == 0) {
			// If we just started out set the current position to S and skip to recursion
			maze[row][col] = 'S';
		} else if (isAtEdge(row, col) && maze[row][col] != '*') {
			// If current position is at the edge but not a wall we found an exit
			maze[row][col] = 'X';

			addExit(row, col);
		} else if (maze[row][col] == '*' || maze[row][col] == '.' || maze[row][col] == 'S') {
			// If current position is a wall or has already been visited, ignore
			return false;
		} else if (maze[row][col] != 'S') {
			// Otherwise set it to visited and continue (but make sure not to overwrite the
			// starting point)
			maze[row][col] = '.';
		}

		// Build the return value by OR-ing together the return values of the recursive calls
		// but fix it to true if we found an exit.

		boolean returnValue = maze[row][col] == 'X';

		// North
		returnValue |= row > 0 && locateExits(row - 1, col, depth + 1);
		// East
		returnValue |= col < (maze[0].length - 1) && locateExits(row, col + 1, depth + 1);
		// South
		returnValue |= row < (maze.length - 1) && locateExits(row + 1, col, depth + 1);
		// West
		returnValue |= col > 0 && locateExits(row, col - 1, depth + 1);

		return returnValue;
	}
	
	public ArrayList<int[]> getListOfExits(){
		return exits;
	}

	public int getMaxRecursionDepth() {
		return maximumRecursionDepth;
	}
	
	public char[][] getMaze(){
		return this.maze;
	}

	/**
	 * This method prints the entire maze in the console for debugging.
	 */
	public void dumpMaze() {
		System.out.println();
		for (int i = 0; i < maze.length; i++) {
			System.out.println(maze[i]);
		}
	}
}