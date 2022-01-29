#include <stdio.h>

char str[80] = "A string to be used for demonstration purposes";

int main(void) 
{
    printf("The third character of the string is: '%c'\n", str[3]); 
    printf("The third character of the string is: '%c'\n", *(str + 3)); 
    printf("The third character of the string is: '%c'\n", *(3 + str)); 
    printf("The third character of the string is: '%c'\n", 3[str]); /* <-- !!! */
    return 0;
}
