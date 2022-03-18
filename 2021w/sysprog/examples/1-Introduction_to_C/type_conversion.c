#include <stdio.h>

int main(void) 
{ 
    
    int i=0,j = 12;   /* i not initialized, only j */ 
    float f1 = 0.,f2 = 1.2; 
    printf("i=%d, j=%d, f1=%f, f2=%f\n", i, j, f1, f2); 
    
    i = (int) f2;   /* explicit: i <- 1, 0.2 lost */ 
    printf("i=%d\n", i); 
    f1 = i;         /* implicit: f1 <- 1.0 */ 
    printf("f1=%f\n", f1); 
    f1 = f2 + (float) j; /* explicit: f1 <- 1.2 + 12.0 */
    printf("f1=%f\n", f1); 
    f1 = f2 + j;    /* implicit: f1 <- 1.2 + 12.0 */ 
    printf("f1=%f\n", f1); 
    
    return 0;
} 
