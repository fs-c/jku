#include <stdio.h>

/* Find bug with call 'valgrind --track-origins=yes -q ./valgrind_test5' */

int main(void) {
	int flag;
	
	/* BUG: variable in condition is not initialized */
	if (flag) {
		printf("Flag was not 0\n");
	} else {
		printf("Flag was 0\n");
	}
	
	return 0;
}
