#include <stdio.h> 

void dosomething(int **ptr); 

int main() 
{ 
    int *p; 
    dosomething(&p);
    printf("%d\n", *p); /* will this work? */
    printf("%d\n", *p); /* and now? */
    return 0;
} 

void dosomething(int **ptr)  /* passed and returned by reference */  
{
    int temp=32+34; 
    *ptr = &temp; 
} 
