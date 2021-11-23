#include <stdio.h> 
#include <string.h> 

char to_upper(char c);
char to_lower(char c);
void process(char *string, char (* processor_function)(char));

int main(void)
{ 
    char example[12] = "hello world";
    process(example, to_upper);   /* pass function pointer */
    printf("to upper: %s\n", example);
    process(example, to_lower);   /* and again */
    printf("to lower: %s\n", example);
    return 0;
} 

void process(char *string, char (* processor_function)(char))
{
    int i, size = strlen(string);
    for (i=0; i<size; i++) {
        string[i] = (*processor_function)(string[i]);
    }
}

char to_upper(char c)
{
    if (c >= 'a' && c <= 'z')
        c += 'A' - 'a';
    return c;
}

char to_lower(char c)
{
    if (c >= 'A' && c <= 'Z')
        c -= 'A' - 'a';
    return c;
}

