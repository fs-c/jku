package watch;

import java.io.IOException;
import java.nio.file.*;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.*;

import static java.nio.file.StandardWatchEventKinds.*;

enum Event {
    NEW_FILE, NEW_DIR, FILE_CREATED, FILE_MODIFIED, FILE_DELETED, DIR_CREATED, DIR_DELETED, START_SEARCH, END_SEARCH, FAILED_SEARCH, WORD_FOUND
}

public class FileWatcher {
    private static final int NUM_THREADS = 5;
    private static final PathMatcher javaMatcher = FileSystems.getDefault().getPathMatcher("glob:**.java");
    private final String word;
    private final Path rootPath;
    private final WatchService watchService;
    private final ExecutorService executorService = Executors.newFixedThreadPool(NUM_THREADS);
    private final CopyOnWriteArraySet<Path> filesWithKeyword = new CopyOnWriteArraySet<>();
    private final Map<Path, WatchKey> pathToKeyMap = new HashMap<>();
    private final Map<Path, Future<?>> pathToTaskMap = new ConcurrentHashMap<>();
    private Thread watchThread;
    private boolean stopWatcher = false;

    public FileWatcher(String rootName, String word) throws IOException {
        this.rootPath = Paths.get(rootName);
        this.word = word;
        this.watchService = FileSystems.getDefault().newWatchService();
    }

    private static void log(Event event, Path path) {
        System.out.println(event.name() + ": " + path.toString());
    }

    private static boolean isJavaFile(Path path) {
        return Files.isRegularFile(path) && javaMatcher.matches(path);
    }

    public void start() throws IOException {
        try (var paths = Files.walk(rootPath.toAbsolutePath())) {
            paths.forEach((path) -> {
                if (Files.isRegularFile(path)) {
                    log(Event.NEW_FILE, path);

                    pathToTaskMap.put(path, executorService.submit(new AnalysisTask(path)));
                } else if (Files.isDirectory(path)) {
                    log(Event.NEW_DIR, path);

                    try {
                        pathToKeyMap.put(path, path.register(watchService, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                }
            });
        }

        this.watchThread = new Thread(new FileWatchRunnable());
        this.watchThread.start();
    }

    public void terminate() {
        try {
            stopWatcher = true;
            watchService.close();
            watchThread.join();
        } catch (InterruptedException | IOException e) {
            throw new RuntimeException(e);
        }

        executorService.shutdown();
    }

    private class FileWatchRunnable implements Runnable {
        private void handlePathEvent(WatchKey key, WatchEvent<Path> event) throws IOException {
            var path = ((Path) key.watchable()).resolve(event.context());
            var kind = event.kind();

            if (kind == ENTRY_CREATE) {
                if (Files.isDirectory(path)) {
                    log(Event.DIR_CREATED, path);

                    pathToKeyMap.put(path, path.register(watchService, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY));
                } else if (isJavaFile(path)) {
                    log(Event.FILE_CREATED, path);

                    pathToTaskMap.put(path, executorService.submit(new AnalysisTask(path)));
                }
            } else if (kind == ENTRY_MODIFY && isJavaFile(path)) {
                log(Event.FILE_MODIFIED, path);

                var existingTask = pathToTaskMap.get(path);

                if (existingTask != null) {
                    existingTask.cancel(true);
                }

                pathToTaskMap.put(path, executorService.submit(new AnalysisTask(path)));
            } else if (kind == ENTRY_DELETE) {
                if (Files.isDirectory(path)) {
                    log(Event.DIR_DELETED, path);

                    var watchKey = Optional.ofNullable(pathToKeyMap.get(path)).orElseThrow();

                    watchKey.cancel();

                    pathToKeyMap.remove(path);
                } else if (isJavaFile(path)) {
                    log(Event.FILE_DELETED, path);

                    var analysisTask = pathToTaskMap.get(path);

                    if (analysisTask != null) {
                        analysisTask.cancel(true);
                    }
                }
            }
        }

        @Override
        public void run() {
            WatchKey key = null;

            while (!stopWatcher) {
                try {
                    key = watchService.take();

                    for (var event : key.pollEvents()) {
                        handlePathEvent(key, (WatchEvent<Path>) event);
                    }
                } catch (ClosedWatchServiceException ignored) {
                    // this is thrown when the watch service is closed while watchService.take is blocking
                } catch (InterruptedException | IOException e) {
                    throw new RuntimeException(e);
                } finally {
                    if (key != null) {
                        key.reset();
                    }
                }
            }
        }
    }

    private class AnalysisTask implements Runnable {
        private final Path filePath;

        private AnalysisTask(Path filePath) {
            this.filePath = filePath;
        }

        @Override
        public void run() {
            log(Event.START_SEARCH, filePath);

            try (var lines = Files.lines(filePath)) {
                // we only care about the first match (or absence thereof)
                var match = lines.filter((line) -> line.contains(word)).findFirst();

                if (match.isPresent()) {
                    log(Event.WORD_FOUND, filePath);

                    filesWithKeyword.add(filePath);
                } else {
                    filesWithKeyword.remove(filePath);
                }

                log(Event.END_SEARCH, filePath);
            } catch (IOException e) {
                log(Event.FAILED_SEARCH, filePath);
            }
        }
    }
}
