#include <stdlib.h>

/* Find bug with call 'valgrind --leak-check=full ./valgrind_test1' */

int main(void) { 
	int *ptr; 

	/* allocate space to hold an int */ 
	ptr = (int*) malloc(sizeof(int)); 

	/* BUG: forgot to free the allocated space */
	/* free(ptr); */
	
	return 0;
}
