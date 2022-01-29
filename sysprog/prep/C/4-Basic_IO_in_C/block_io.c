#include <stdio.h>
#include <stdlib.h>

#define FILENAME "integers.bin"
#define ARRAY_SIZE 10

/**
 * Saves and reads back an array of integers.
 * 
 * Have a look at the file 'integers.bin' after running the program,
 * to see that this is indeed a binary file (rather than a text one).
 */
int main()
{
    FILE *file = NULL;
    int static_array[ARRAY_SIZE];
    int *dynamic_array = NULL;
    size_t count;
    int i;

    /* populate the array with numbers */
    for (i = 0; i < ARRAY_SIZE; i++) {
        static_array[i] = i;
    }

    /* open the file and save the numbers */
    file = fopen(FILENAME, "w");
    if (file == NULL) {
        fprintf(stderr, "Failed to open file '%s' for writing.\n", FILENAME);
        exit(1);
    }
    count = fwrite(static_array, sizeof(int), ARRAY_SIZE, file);
    printf("Wrote %lu integers to file '%s'\n", count, FILENAME);
    fclose(file);

    /* allocate memory to hold the numbers when they are read back in */
    dynamic_array = (int *)malloc(ARRAY_SIZE * sizeof(int));
    if (dynamic_array == NULL) {
        fprintf(stderr, "Failed to allocate memory for the dynamic array.\n");
        exit(1);
    }

    /* open the file and read the numbers into the dynamically allocated array */
    file = fopen(FILENAME, "r");
    if (file == NULL) {
        fprintf(stderr, "Failed to open file '%s' for reading.\n", FILENAME);
        free(dynamic_array);
        exit(1);
    }
    count = fread(dynamic_array, sizeof(int), ARRAY_SIZE, file);
    printf("Read %lu integers from file '%s'\n", count, FILENAME);
    fclose(file);

    /* print out the numbers */
    printf("The numbers read: ");
    for (i = 0; i < ARRAY_SIZE; i++) {
        printf("%d ", dynamic_array[i]);
    }
    printf("\n");
    
    free(dynamic_array);

    return 0;
}

