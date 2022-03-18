#include <stdio.h>
#include <string.h>

struct person 
{
    char lname[20];     /* last name */
    char fname[20];     /* first name */
    int age;            /* age */
    float rate;         /* e.g. 12.75 per hour */
};

/* declare the structure my_struct */
struct person my_struct; 

int main(void) 
{
    strcpy(my_struct.lname, "Jensen");
    strcpy(my_struct.fname, "Adam");
    printf("\n%s ", my_struct.fname);
    printf("%s\n", my_struct.lname);
    
    return 0;
}
