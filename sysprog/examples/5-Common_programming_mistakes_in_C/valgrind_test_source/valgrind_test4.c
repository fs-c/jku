#include <stdlib.h>

/* Find bug with call 'valgrind -q ./valgrind_test4' */

int main(void) { 
	int *ptr; 

	/* allocate space to hold an int */ 
	ptr = (int*) malloc(sizeof(int)); 

	/* write inside allocated memory */
	*ptr = 20;

	/* read inside allocated memory */
	*ptr = *ptr + 10;
	
	/* BUG: read outside allocated memory */
	*ptr = *(ptr+1);
	
	/* BUG: write outside allocated memory */
	*(ptr+1) = 25;
	
	return 0;
}
