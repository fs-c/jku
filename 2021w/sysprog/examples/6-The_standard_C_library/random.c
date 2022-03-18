#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int main(void) {

	printf("RAND_MAX on your machine is %d\n", RAND_MAX);
	printf("The next random number between 0 and RAND_MAX is %d\n", rand());
	printf("and the next: %d\n", rand());
	printf("and another one: %d\n\n", rand());

	srand(1);
	printf("The same sequence again %d\n", rand());
	printf("and the next: %d\n", rand());
	printf("and another one: %d\n\n", rand());

	srand(1);
	printf("Here you can see in which order the parameters to printf are evaluated: %d, %d, %d\n\n", rand(), rand(), rand());

	srand(time(0));
	printf("Correctly seeded random number generator (RNG) produces %d\n", rand());
	printf("and the next: %d\n", rand());
	printf("and another one: %d\n\n", rand());

	return 0;
}
