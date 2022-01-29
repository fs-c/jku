/* Enable GNU extensions: needed for fcloseall() */
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Normal exit codes */
#define ERROR_NO_SEARCH_STRING    -1 
#define ERROR_CANNOT_OPEN_FILE    -2
#define ERROR_WHILE_READING       -3
#define ERROR_WHILE_WRITING       -4

/* Normal exit codes */
#define NO_ERROR_STRING_FOUND      0
#define NO_ERROR_STRING_NOT_FOUND  1

void usage(char *exe_name);

/**
 * Reads lines from a specified file or from stdin, and prints the lines
 * that contain a provided search string at least once, prefixed by the 
 * line number.
 */
int main(int argc, char *argv[])
{
    FILE *in;
    char *search_str = NULL;
    char *line = NULL;
    int line_number = 0, found = NO_ERROR_STRING_NOT_FOUND;
    size_t num_chars = 0;

    if (argc < 2 || argc > 3) {
        usage(argv[0]);
        exit(ERROR_NO_SEARCH_STRING);
    }
    search_str = argv[1];

    if (argc == 3) {
        in = fopen(argv[2], "r");
        if (in == NULL) {
            fprintf(stderr, "Error while trying to open file '%s'.\n", argv[2]);
            exit(ERROR_CANNOT_OPEN_FILE);
        }
    } else {
        in = stdin;
    }

    while (!feof(in)) {
        line_number++;
        getline(&line, &num_chars, in);
        if (ferror(in)) {
            fprintf(stderr, "Error while trying to read line %d from file '%s'.\n", line_number, argv[2]);
            fcloseall();
            exit(ERROR_WHILE_READING);
        }
        if (strstr(line, search_str) != NULL) {
            found = NO_ERROR_STRING_FOUND;
            printf("%d : %s", line_number, line);
            if (ferror(stdout)) {
                fprintf(stderr, "Error while trying to write line %d to the standard output.\n", line_number);
            }
        }
        free(line);
        line = NULL;
        num_chars = 0;
    }

    fcloseall();

    return found;
}

void usage(char *exe_name)
{
    printf("%s usage:\n", exe_name);
    printf("\t%s search_word [file]\n", exe_name);
    printf("\t%s \"search phrase\" [file]\n\n", exe_name);
}

