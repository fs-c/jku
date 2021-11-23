
#include <stdio.h>
#include <stdlib.h>

#define COLS 5

int (*xptr)[COLS];

int main(void) 
{
    int nrows = 10;
    int row, col;
    
    xptr = (int(*)[COLS])malloc(nrows * COLS * sizeof(int));
    
    for (row = 0; row < nrows; row++) {
        for (col = 0; col < COLS; col++) {
            xptr[row][col] = 1;
        }
    }
    free(xptr);
    
    return 0;
}
