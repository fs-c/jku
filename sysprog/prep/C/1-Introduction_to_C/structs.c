#include <stdio.h> 

struct birthday 
{ 
    int month; 
    int day; 
    int year; 
}; 

int main() 
{ 
    struct birthday birth; /* - no 'new' needed */ 
                           /* then, it's just like Java! */ 
    birth.day=1; 
    birth.month=1; 
    birth.year=2003; 
    printf("I was born on %d/%d/%d", birth.day, birth.month, birth.year); 
    
    return 0;
} 
