#include <stdio.h>

#define ROWS 5
#define COLS 10

int multi[ROWS][COLS];

void init_array(int array[][COLS], int value);

int main(void) 
{

    int row, col;

    init_array(multi, 1);
    
    for (row = 0; row < ROWS; row++) {
        for (col = 0; col < COLS; col++) {
            printf("%d ",multi[row][col]);
        }
        printf("\n");
    }
    
    return 0;
}

void init_array(int array[][COLS], int value) {
    int row, col;
    for (row = 0; row < ROWS; row++) {
        for (col = 0; col < COLS; col++) {
            array[row][col] = value;
        }
    }
}
