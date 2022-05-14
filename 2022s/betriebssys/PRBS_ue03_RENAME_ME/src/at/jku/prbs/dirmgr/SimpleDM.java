package at.jku.prbs.dirmgr;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;

public class SimpleDM extends AbstractDirectoryManager {

	public SimpleDM(String path) {
		super(path);
	}

	@Override
	public ArrayList<String> readDir(final String subPath) throws IOException {
		ArrayList<String> directoryFiller = new ArrayList<String>();
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
	
		// Read directory
        DirectoryStream<Path> directoryStream = Files.newDirectoryStream(absPath);
        
    	// Fill the wrapper with all entries
        for (Path p : directoryStream) {
        	Path rootDir = Paths.get(mDirectoryPath);
        	directoryFiller.add(rootDir.relativize(p).toString());
        }
        
        return directoryFiller;
	}
	
	@Override
	public BasicFileAttributes getFileAttributes(final String subPath) throws IOException {		
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		BasicFileAttributes returnVal = null;
		
		// If file does not exist, throw an exception
		if (!Files.exists(absPath, LinkOption.NOFOLLOW_LINKS)) {
			throw new FileNotFoundException("File not found");
		} else {
			// Read attributes from file
			returnVal = Files.readAttributes(absPath, BasicFileAttributes.class);
		}
		
		return returnVal;
	}

	@Override
	public void createFile(String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		// If file already exists, throw an IO exception
		if (Files.exists(absPath)) {
			throw new FileAlreadyExistsException("File already exists");
		} else {
			// Create new file
			Files.createFile(absPath);
		}
	}

	@Override
	public void deleteFile(String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		// If file does not exist, throw an exception
		if (!Files.exists(absPath, LinkOption.NOFOLLOW_LINKS)) {
			throw new FileNotFoundException("File not found");
		} else {
			// Delete file
			Files.delete(absPath);
		}
	}

	@Override
	public void renameFile(String subPathOld, String subPathNew) throws IOException {		
		Path absPathOld = getAbsoluteAndNormalizedPath(subPathOld);
		Path absPathNew = getAbsoluteAndNormalizedPath(subPathNew);

		if (!Files.exists(absPathOld, LinkOption.NOFOLLOW_LINKS)) {
			throw new FileNotFoundException("File not found");
		}
		
		// Move renames the file, overwriting any existing file
		Files.move(absPathOld, absPathNew, StandardCopyOption.REPLACE_EXISTING);	
	}
	

	@Override
	public void createDirectory(String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		// If file already exists, throw an IO exception
		if (Files.exists(absPath)) {
			throw new FileAlreadyExistsException("Directory already exists");
		} else {
			// Create new directory
			Files.createDirectory(absPath);
		}
	}

	@Override
	public void deleteDirectory(String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		// Remove the directory if it exists, otherwise return an error code
		if (!Files.exists(absPath)) {
			throw new FileAlreadyExistsException("Directory not found");
		} else if (Files.isDirectory(absPath)){
			// If path points to a directory, recursively delete the whole content
			Files.walkFileTree(absPath, new DeleteAllFilesVisitor());
		} 
	}
}
