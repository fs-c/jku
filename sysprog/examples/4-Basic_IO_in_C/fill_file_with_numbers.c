#include <stdio.h>
#include <stdlib.h>

#define FILENAME "output.txt"
#define DEFAULT_REPETITIONS  5

/**
 * Creates and fills the file 'output.txt' with numbers. It can read from
 * the command line the number of numbers to put into the file. The default
 * is 5.
 */
int main(int argc, char *argv[])
{
    int i, reps = DEFAULT_REPETITIONS, num;
    FILE *stream;

    /* read the number of repetitions from the command line if available */
    if (argc > 1) {
        int result = sscanf(argv[1], "%d", &reps);
        if (result < 1 || reps < 1) {
            fprintf(stderr, "Invalid number of repetitions provided at the command line.\n");
            exit(1);
        }
    }

    /* open the file for writing and write the number 1 into it */
    stream = fopen(FILENAME, "w");
    if (stream == NULL) {
        fprintf(stderr, "Failed to open %s for writing.\n", FILENAME);
        exit(1);
    }
    fprintf(stream, "1 ");
    fclose(stream);

    /* open the file as many times as specified in the command line, 
       and each time append the "next" number to the end --
       NOTE: it is *not* actually necessary to close and open the 
       file every time, this is only done here for demonstration
       purposes */
    for (i = 0; i < reps-1; i++) {
        stream = fopen(FILENAME, "r+");
        if (stream == NULL) {
            fprintf(stderr, "Failed to open %s for reading and writing.\n", FILENAME);
            exit(1);
        }
        while (!feof(stream)) {
            fscanf(stream, "%d", &num);
        }
        fprintf(stream, "%d ", num+1);
        fclose(stream);
    }
    
    return 0;
}
