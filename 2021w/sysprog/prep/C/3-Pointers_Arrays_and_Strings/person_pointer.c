#include <stdio.h>
#include <string.h>

/* the structure type */
struct person       
{
    char lname[20]; /* last name */
    char fname[20]; /* first name */
    int age;        /* age */
    float rate;     /* e.g. 12.75 per hour */
};

/* define the structure */
struct person my_struct; 

/* function prototype */
void show_name(struct person *p); 


int main(void) 
{
    struct person *st_ptr;  /* a pointer to a structure */
    st_ptr = &my_struct;    /* point the pointer to my_struct */

    strcpy(my_struct.lname, "Jensen");
    strcpy(my_struct.fname, "Adam");
    printf("\n%s ", my_struct.fname);
    printf("%s\n", my_struct.lname);

    my_struct.age = 27;
    show_name(st_ptr);      /* pass the pointer */
    
    return 0;
}

/* access the structure through a pointer */
void show_name(struct person *p) 
{
    printf("\n%s ", p->fname); 
    printf("%s ", p->lname);
    printf("%d\n", p->age);
}
