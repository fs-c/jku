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

/**
 * Sets the date of the pinted to structure to February 1st 2004.
 */
void set_date(struct date* dptr) 
{
    dptr->day = 1;
    dptr->month = 2;
    dptr->year = 2004;
}


int main (void) 
{
    struct date_time date_time_instance;
        
    /* "pretend" that date_time_instance is of type struct date */
    set_date((struct date *)&date_time_instance);
    
    /* print out the result */
    printf("day: %d\n", date_time_instance.date.day);
    printf("month: %d\n", date_time_instance.date.month);
    printf("year: %d\n", date_time_instance.date.year);
    
    return 0;
}

