#include <stdio.h>
#include <stddef.h>

struct date { 
    int day; 
    int month; 
    int year; 
};

int main (void) 
{
    printf("offset of date.day: %lu\n", offsetof(struct date, day));
    printf("offset of date.month: %lu\n", offsetof(struct date, month));
    printf("offset of date.year: %lu\n", offsetof(struct date, year));
    
    return 0;
}
