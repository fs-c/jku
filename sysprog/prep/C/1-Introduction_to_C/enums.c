#include <stdio.h>

enum days  {Mon, Tues, Weds, Thurs, Fri, Sat, Sun };

int main(void) 
{
    enum days start, end;
    
    start = Weds;
    end = Sat;
    
    printf ("start = %d end = %d\n",start,end);
    
    start = 42;
    printf ("start now equals %d\n",start);
    
    return 0;
}
