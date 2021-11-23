#include <stdio.h> 

int main(void) 
{ 
    int nstudents = 0; /* Initialization, required */ 

    printf("How many students does Uni-Linz have? "); 
    scanf ("%d", &nstudents); /* Read input */ 
    printf("Uni-Linz has %d students.\n", nstudents); 
    
    return 0;
} 
