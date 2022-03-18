#include <stddef.h>
#include <stdio.h>

struct date { 
    int day; 
    int month; 
    int year; 
};

struct date_time {
    struct date date;
    int hour;
    int minute;
    int second;
};

int main (void) 
{
    printf("offset of date.day: %lu\n", offsetof(struct date, day));
    printf("offset of date.month: %lu\n", offsetof(struct date, month));
    printf("offset of date.year: %lu\n", offsetof(struct date, year));

    printf("offset of date_time.date.day: %lu\n", offsetof(struct date_time, date.day));
    printf("offset of date_time.date.month: %lu\n", offsetof(struct date_time, date.month));
    printf("offset of date_time.date.year: %lu\n", offsetof(struct date_time, date.year));
    
    return 0;
}
