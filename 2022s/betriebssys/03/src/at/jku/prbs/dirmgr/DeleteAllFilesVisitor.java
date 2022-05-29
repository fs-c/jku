package at.jku.prbs.dirmgr;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;

public class DeleteAllFilesVisitor extends SimpleFileVisitor<Path> {
	
	@Override
	public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
		// Delete file in directory
		Files.delete(file);
		return FileVisitResult.CONTINUE;
	}

	@Override
	public FileVisitResult postVisitDirectory(Path dir, IOException e) throws IOException {
		if (e != null) {
			// Deleting files in this directory failed with an exception
			// => raise that exception to indicate failure
			throw e;
		}
		
		// Eventually delete empty directory
		Files.delete(dir);
		return FileVisitResult.CONTINUE;
	}
}
