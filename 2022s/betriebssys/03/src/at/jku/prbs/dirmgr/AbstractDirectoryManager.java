package at.jku.prbs.dirmgr;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;

public abstract class AbstractDirectoryManager implements DirectoryManager {

	protected String mDirectoryPath;

	public AbstractDirectoryManager(String path) {
		mDirectoryPath = path;
	}
	
	/**
	 * Update the given path in our HashFS to the absolute, normalized path.
	 * @param subPath Sub-path within our managed directory file system
	 * @return absolute path in the original file system
	 */
	protected Path getAbsoluteAndNormalizedPath(String subPath) {
		return Paths.get(mDirectoryPath, subPath).normalize().toAbsolutePath();
	}
	

	@Override
	public abstract ArrayList<String> readDir(final String subPath) throws IOException;
	
	@Override
	public abstract BasicFileAttributes getFileAttributes(final String subPath) throws IOException;
	
	@Override
	public abstract void createFile(String subPath) throws IOException;

	@Override
	public abstract void deleteFile(String subPath) throws IOException;

	@Override
	public abstract void renameFile(String subPathOld, String subPathNew) throws IOException;
}
