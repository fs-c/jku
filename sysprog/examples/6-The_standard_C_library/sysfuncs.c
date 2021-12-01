#include <stdio.h>
#include <stdlib.h>

void run_at_exit(void) {
	printf("IN EXIT CALLBACK: Here we could perform some cleanup operations like closing files or freeing memory\n");
}

int main(void) {

	int retCode;

	printf("Calling UNIX program 'ls'\n");
	retCode = system("ls -l");
	printf ("Return value was %d\n\n", retCode);

	printf("Calling non-existing program 'dsfjksjkf'\n");
	retCode = system("dsfjksjkf");
	printf ("Return value was %d\n\n", retCode);

	/* Flush buffer of stderr because otherwise the error message */
	/* of 'system("dsfjksjkf")' gets printed too late. */
	fflush(stderr);

	/* Register function to be run upon exiting the program */
	if(!atexit(run_at_exit)) {
		printf("Exit callback successfully registered\n");
	} else {
		fprintf(stderr, "Exit callback could not be registered\n");
	}

	printf("Now, let's exit the program\n");
	exit(1);

	printf("This output should not be printed any more\n");

	return 0;
}
