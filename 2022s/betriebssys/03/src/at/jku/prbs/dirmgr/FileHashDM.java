package at.jku.prbs.dirmgr;


import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;

import at.mroland.utils.StringUtils;

public class FileHashDM extends SimpleDM {
	
	public static final String LOG_FILE_NAME = ".hashdm";              // Log file name
	
	public static final String XATTR_FILE_HASH_ALGORITHM = "SHA-256";  // Hash algorithm used for the hash attribute
	public static final int XATTR_FILE_HASH_LENGTH = 32;               // Length of hash value in bytes
	
	// Log event strings
	private static final String LOG_EVENT_DELETE_FILE_BEFORE = "Deleting file";
	private static final String LOG_EVENT_DELETE_DIR_BEFORE = "Deleting directory";
	private static final String LOG_EVENT_CREATE_FILE_AFTER = "File created";
	private static final String LOG_EVENT_CREATE_DIR_AFTER = "Directory created";
	private static final String LOG_EVENT_MOVE_BEFORE = "Moving file";
	private static final String LOG_EVENT_MOVE_AFTER = "New file name";

	// Formatter for log time stamps
	private static final SimpleDateFormat LOG_TIMESTAMP_FORMATTER = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
	
	private final MessageDigest hashDigest;  // Message digest used for hashing
	
	
	public FileHashDM(String dirPath) throws NoSuchAlgorithmException {
		super(dirPath);
		hashDigest = MessageDigest.getInstance(XATTR_FILE_HASH_ALGORITHM);
	}

	
	/**
	 * Computes the hash over the data of a given file.
	 * 
	 * @param subPath Path to the file for which a hash should be computed
	 * @return Computed hash value as byte array
	 * @throws IOException
	 */
	protected byte[] computeHash(final String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		InputStream fileStream = Files.newInputStream(absPath);
		
		int bytesRead;
		byte[] buffer = new byte[1024];
		try {
			// Read data until EOF
			while ((bytesRead = fileStream.read(buffer)) > 0) {
				// Feed the read chunk into the hash buffer
				hashDigest.update(buffer, 0, bytesRead);
			}
		} finally {
			try { fileStream.close(); } catch (IOException ignore) {}
		}

		// Compute the hash value
		byte[] hashValue = hashDigest.digest();
			
		// Reset the hash algorithm instance for the next use
		hashDigest.reset();
		
		return hashValue;
	}


	/**
	 * Computes the hash over the data of a given file.
	 * 
	 * @param subPath Path to the file for which a hash should be computed
	 * @return Computed hash value as byte array
	 * @throws IOException
	 */
	public byte[] getFileHash(final String subPath) throws IOException {
		Path absPath = getAbsoluteAndNormalizedPath(subPath);
		
		byte[] hash = null;
		
		// If file does not exist, throw an exception
		if (!Files.exists(absPath, LinkOption.NOFOLLOW_LINKS)) {
			throw new FileNotFoundException("File not found");
		} else if (!Files.isRegularFile(absPath)) {
			// Hash can only be computed for a regular file
			throw new InvalidPathException(absPath.toString(), "Not a regular file");
		} else {
			// Compute the hash value
			hash = computeHash(subPath);
		}
		
		return hash;
	}


	@Override
	public void createFile(String subPath) throws IOException {
		super.createFile(subPath);
		logEvent(subPath, LOG_EVENT_CREATE_FILE_AFTER, true);
	}

	@Override
	public void deleteFile(String subPath) throws IOException {
		logEvent(subPath, LOG_EVENT_DELETE_FILE_BEFORE, true);
		super.deleteFile(subPath);
	}

	@Override
	public void renameFile(String subPathOld, String subPathNew) throws IOException {
		logEvent(subPathOld, LOG_EVENT_MOVE_BEFORE, true);	
		super.renameFile(subPathOld, subPathNew);
		logEvent(subPathNew, LOG_EVENT_MOVE_AFTER, false);	
	}

	@Override
	public void createDirectory(String subPath) throws IOException {
		super.createDirectory(subPath);
		logEvent(subPath, LOG_EVENT_CREATE_DIR_AFTER, false);
	}

	@Override
	public void deleteDirectory(String subPath) throws IOException {
		logEvent(subPath, LOG_EVENT_DELETE_DIR_BEFORE, false);
		super.deleteDirectory(subPath);
	}
	
	/**
	 * Add event to the log file in the root directory.
	 * 
	 * In case a directory got modified, the event shall be added to the parent directory.
	 * 
	 * @param path Path to the file that was modified/created/deleted. This is the absolute path to the actual file system. 
	 * @param eventType Type of the event
	 * @return Status code of saving the logging event (0 = success, negative value = error)
	 */
	private int logEvent(final String subPath, final String eventType, final boolean includeHash) {
		Path logFile = Paths.get(mDirectoryPath, LOG_FILE_NAME);
		
		int result = 0;
		
		String fileHash = null;
		if (includeHash) {
			try {
				fileHash = StringUtils.bytesToHex(getFileHash(subPath));
			} catch (IOException e) {
				// Could not create the file hash, proceed with empty hash
				fileHash = null;
				result = -2;
			}
		}
		
		String timestamp = LOG_TIMESTAMP_FORMATTER.format(new Date());
		String logEntry = String.format("[%s] %s: '%s' %s\n",
				                        timestamp,
				                        eventType,
				                        subPath,
				                        (includeHash ? fileHash : ""));
		
		BufferedWriter fileWriter = null;
		try {
			// Open file for writing
			fileWriter = Files.newBufferedWriter(logFile,
                                                 StandardOpenOption.WRITE,
                                                 StandardOpenOption.APPEND,
                                                 StandardOpenOption.CREATE);
			// Write the log line to the file
			fileWriter.write(logEntry);
		} catch (IOException e) {
			// Could not write log event
			result = -1;
		} finally {
			// Flush the written data and close the file
			if (fileWriter != null) {
				try { fileWriter.close(); } catch (IOException ignore) {}
			}
		}
		
		return result;
	}
	
	public static void main(String[] args) {
		if (args.length < 1) {
			System.err.println("Usage: FileHashDM <directory path>");
			System.exit(1);
			return;
			
		} else if (args.length == 1) {
			FileHashDM testDM;
			
			try {
				testDM = new FileHashDM(args[0]);
			} catch (NoSuchAlgorithmException e) {
				e.printStackTrace();
				System.exit(2);
				return;
			}

			// Test the directory manager by creating multiple files and deleting them again
			try {
				testDM.createFile("testFile.txt");
				testDM.createDirectory("testDir");
				
				testDM.createFile("testDir/testSubFile.txt");
				testDM.createFile("testDir/testSubFile2.txt");
				testDM.createDirectory("testDir/subDir");
				testDM.createFile("testDir/subDir/subSubFile.txt");
				
				testDM.renameFile("testDir/testSubFile.txt", "testDir/testFileRenamed.txt");
				
				ArrayList<String> listing = testDM.readDir(".");
				System.out.println("List of files in the root directory:");
				for (String string : listing) {
					System.out.println(string);
				}
				
				listing = testDM.readDir("testDir");
				System.out.println("\nFile-listing of the sub-directory:");
				for (String string : listing) {
					System.out.println(string);
				}
			} catch (IOException e) {
				e.printStackTrace();
			} finally {
				try {
					testDM.deleteFile("testFile.txt");
					testDM.deleteDirectory("testDir");
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
	}
}
