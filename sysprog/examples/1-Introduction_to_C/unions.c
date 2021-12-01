#include <stdio.h>
#include <stddef.h>

union variable { 
    char character; 
    int number_int; 
    float number_float; 
    double number_double; 
};

int main (void) 
{
    union variable var;
    
    printf("size of union variable: %lu\n", sizeof(union variable));
    printf("size of double: %lu\n", sizeof(double));
    
    printf("offset of variable.character: %lu\n", offsetof(union variable, character));
    printf("offset of variable.number_int: %lu\n", offsetof(union variable, number_int));
    printf("offset of variable.number_float: %lu\n", offsetof(union variable, number_float));
    printf("offset of variable.number_double: %lu\n", offsetof(union variable, number_double));

    var.number_double = 30.7;
    
    printf("value of variable.double: %f\n", var.number_double);
    printf("value of variable.character: %d\n", var.character);
        
    return 0;
}
