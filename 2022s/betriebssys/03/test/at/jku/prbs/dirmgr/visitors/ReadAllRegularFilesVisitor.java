package at.jku.prbs.dirmgr.visitors;

import java.io.File;
import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;

public class ReadAllRegularFilesVisitor extends SimpleFileVisitor<Path> {
	
	// List of paths, matching the search criterion  
	private final ArrayList<String> results;
	
	// Root directory of the mirrored file system path 
	private final Path rootDir;
	
	public ReadAllRegularFilesVisitor(Path rootDir)  {
		results = new ArrayList<>();
		this.rootDir = rootDir;
	}

	@Override
	public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
		
		if(Files.isRegularFile(file)){
			String relativeFileName = File.separator + rootDir.relativize(file).toString();
	
			results.add(relativeFileName);
		}
		return FileVisitResult.CONTINUE;
	}

	@Override
	public FileVisitResult visitFileFailed(Path file, IOException exc) {
		System.err.println(exc);
		return FileVisitResult.CONTINUE;
	}

	public String[] getResults() {
		String[] res = new String[results.size()];
		return results.toArray(res);
	}
}
