#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/**
 * Reads in lines of comma-separated integers, sums them and prints them out
 *
 * Run with ./csv_file_reader < numbers.csv
 */
int main()
{
    char *line = NULL;
    size_t num_chars = 0;
    ssize_t result = 0;
    int current_number = 0, sum = 0, line_number = 0;
    char *str_ptr;

    while (!feof(stdin)) {
        line_number ++;
        sum = 0;
        /* read in the next line */
        result = getline(&line, &num_chars, stdin);
        if (result < 0) {
            if (feof(stdin)) {
                break;
            } else {
                fprintf(stderr, "Error while reading input at line %d.\n", line_number);
                exit(1);
            }
        }
        /* check if we have an empty line (only newline, or no chars at all) */
        if (strlen(line) > 1) {
            /* "split" the string and use sscanf to convert the numbers */
            str_ptr = line;
            while (*str_ptr != '\0') {
                /* try to read in the next number */
                int args_assigned = sscanf(str_ptr, "%i", &current_number);
                if (args_assigned != 1) {
                    fprintf(stderr, "!!! Argument that is not a number encountered on line %d: %s",
                        line_number, line);
                    break;
                }
                sum += current_number;
                /* progress to the next comma, or the end of the line */
                while (*str_ptr != ',' && *str_ptr != '\0') 
                    str_ptr++;
                /* if we are at a comma, go one character further */
                if (*str_ptr == ',')
                    str_ptr++;
            }
            /* if we have reached the end of the line string, we have a valid sum */
            if (*str_ptr == '\0') {
                printf("Sum of line %d: %d\n", line_number, sum);
            }
        }

        /* reset the line's storage space */
        free(line);
        line = NULL;
        num_chars = 0;
    }

    return 0;
}


