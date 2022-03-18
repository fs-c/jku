#include <stdlib.h>

/* Find bug with call 'valgrind -q ./valgrind_test2' */

int main(void) { 
	int *ptr; 

	/* allocate space to hold an int */ 
	ptr = (int*) malloc(sizeof(int)); 

	/* free the allocated space */
	free(ptr);
	free(ptr);	/* BUG: memory already freed */
	
	return 0;
}
