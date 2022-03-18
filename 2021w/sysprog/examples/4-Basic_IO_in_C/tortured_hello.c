#include <stdio.h>

/**
 * Prints 'hello world' to the standard output using several
 * output functions.
 */
int main()
{
    fputc('h', stdout);
    putc('e', stdout);
    putchar('l');
    fputs("lo ", stdout);
    puts("world"); /* automatically adds a newline at the end */

    return 0;
}
