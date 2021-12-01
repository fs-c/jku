#include <stdio.h> 
#include <stdint.h>

#include "power.h"

int main(void) { 
	int res;
	res = power(2,3);
	printf("2^3 = %d\n", res);
	printf("3^2 = %d\n", power(3, 2));
	return 0;
} 
