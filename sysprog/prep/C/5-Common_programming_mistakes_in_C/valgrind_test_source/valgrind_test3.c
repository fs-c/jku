#include <stdlib.h>

/* Find bug with call 'valgrind -q ./valgrind_test3' */

int main(void) { 
	int numbers[4] = {1, 2, 3, 4};
	
	int removeToGetNiceSigSegv = 0;

	/* write inside array */
	numbers[0] = 4;

	/* read inside array */
	numbers[0] = numbers[0] - 3;
	
	/* BUG: read outside array */
	/* goes unnoticed if removeToGetNiceSigSegv exists */
	numbers[3] = numbers[4];
	
	/* BUG: write outside array */
	/* goes unnoticed if removeToGetNiceSigSegv exists */
	numbers[4] = 5;
	
	return 0;
}
