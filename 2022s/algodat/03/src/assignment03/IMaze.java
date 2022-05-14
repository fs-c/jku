package assignment03;

import java.util.ArrayList;

public interface IMaze {
	/** 
	 * This method represents the recursive algorithm to find the exits.
	 * Note: The first call of this method shall define the starting point given by
 	 *       the parameters row and col, which shall be marked with character 'S'.
	 *  
	 * @param row defines the row of the current position
	 * @param col defines the column of the current position
	 * @param depth represents the current recursion depth
	 * @return True is returned if at least one exit has been found, or false otherwise.
	 * @throws IllegalArgumentException if row or column are out of array bounds.
	 */
	public boolean locateExits(int row, int col, int depth) throws IllegalArgumentException;
	
	/**
	 * This method returns the list of row-column-coordinates of found exits. The
	 * coordinates are stored in int[] (1st element row, 2nd element column) and
	 * finally collected in an ArrayList.
	 * 
	 * @return list of found exists. If there are no exits the list shall
	 * be empty. 
	 */
	public ArrayList<int[]> getListOfExits();
	
	/**
	 * This method returns the maximum recursion depth after the maze has been analyzed 
	 * with locateExists(), otherwise -1 is returned.
	 * 
	 * @return the maximum recursion depth, or -1 if maze has not yet been analyzed.
	 */
	public int getMaxRecursionDepth();
	
	/**
	 * This method returns maze:
	 *   before call of locateExits(): the unchanged maze that has been passed as parameter in the constructor.
	 *   after call of locateExits(): the maze after it has been changed by your algorithm.
	 *  
	 * @return the maze
	 */
	public char[][] getMaze();

}
