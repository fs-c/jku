package at.jku.prbs.dirmgr;

import java.io.IOException;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;

public interface DirectoryManager {
	
	/**
	 * List the files within the given sub-directory 
	 * @param subPath Path to the sub-directory within the DM root path
	 * @return List of files and directories within given sub-directory
	 * @throws IOException
	 */
	ArrayList<String> readDir(String subPath) throws IOException;

	/**
	 * Get the file attributes of a file 
	 * @param subPath Path to the file that should be read (relative to DM root path).
	 * @return Attributes of the file
	 * @throws IOException
	 */
	BasicFileAttributes getFileAttributes(String subPath) throws IOException;

	/**
	 * Create a file within the given DM root path.
	 * @param subPath Path to the file that should be created (relative to DM root path).
	 * @throws IOException
	 */
	void createFile(String subPath) throws IOException;

	/**
	 * Delete a file within the given DM root path.
	 * @param subPath Path to the file that should be deleted (relative to DM root path).
	 * @throws IOException
	 */
	void deleteFile(String subPath) throws IOException;
	
	/**
	 * Rename a given file 
	 * @param subPathOld Path to the file that should be renamed (relative to DM root path).
	 * @param subPathNew Path to the new file (relative to DM root path).
	 * @throws IOException
	 */
	void renameFile(String subPathOld, String subPathNew) throws IOException;
	

	void createDirectory(String subPath) throws IOException;

	void deleteDirectory(String subPath) throws IOException;
}
