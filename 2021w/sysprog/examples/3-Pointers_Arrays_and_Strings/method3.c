#include <stdio.h>
#include <stdlib.h>

int main(void) 
{
    int nrows = 5;  /* Both nrows and ncols could be evaluated */
    int ncols = 10; /* or read in at run time */

    int row;
    int **rowptr;
    rowptr = (int**)malloc(nrows * sizeof(int *));
    if (rowptr == NULL) {
        puts("Failure to allocate room for row pointers.\n");
        exit(0);
    }
    printf("Index Pointer(hex) Pointer(dec) Diff.(dec)");
    for (row = 0; row < nrows; row++) { 
        rowptr[row] = (int*)malloc(ncols * sizeof(int));
        if (rowptr[row] == NULL) {
            printf("\nFailure to allocate for row[%d]\n",row);
            exit(0);
        }
        printf("\n%5d %12p %12lu", row, rowptr[row], (long) rowptr[row]);
        if (row > 0)
            printf(" %9d",(int)(rowptr[row] - rowptr[row-1]));
    }
    
    /* finally, we deallocate the memory */
    for (row = 0; row < nrows; row++) {
        free(rowptr[row]);
    }
    free(rowptr);
    printf("\n");
    return 0;
}
