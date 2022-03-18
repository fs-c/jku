#include <stdio.h>

enum enum1 {A, B, C };
/* C cannot be used again, as enums (unlike structs) are not a separate namespace! */
enum enum2 {/*C,*/ D, E, F };

void f1(enum enum1 param, char *text) {
	printf("f1 called with %d and %s\n", param, text);
}

void f2(enum enum2 param, char *text) {
	printf("f2 called with %d and %s\n", param, text);
}


int main(void) 
{
    enum enum1 one;
    enum enum2 two;
	enum enum1 A;
    
    one = C;
    two = D;
    printf ("One-C = %d, Two-D = %d\n\n",one,two);

    one = A;	/* Warning: A is uninitialized --> variable A, not enum element A! */
    printf ("One-A = %d\n",one); /* Could produce e.g. 32766 */

    A = C;
    printf ("A-C = %d\n",A);

    one = A;	/* Expected: 0, Result: 2; you get the variable content, not the enum constant */
    printf ("One-A = %d\n\n",one);
	one = C;	/* Reset it back to original value from above */
	
	f1(one, "one");
	f2(two, "two");
	/* This does work, as enums are not really types but ints -> we can supply any kind of enum as parameter! */
	f1(two, "two");
	f2(one, "one");
    
    return 0;
}
