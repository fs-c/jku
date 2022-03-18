#include <stdio.h>
#include <string.h>

/* Find bug with call 'valgrind -q ./valgrind_test6' */

int main(void) {
	
	/* BUG: No space left for trailing '\0' */
	char string[5] = "Hello";
	
	/* strlen doesn't find end of string and keeps counting until it *
	 * finds a '\0' in memory (possibly creating a read violation)   */
	printf("Our string is %lu characters long\n", strlen(string));
	
	return 0;
}
