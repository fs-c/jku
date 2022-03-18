#include <stdio.h> 

/* program called with command-line parameters */ 
int main(int argc, char *argv[]) 
{ 
	int ctr; 

	for (ctr = 0; ctr < argc; ctr = ctr + 1) { 
		printf("Argument #%d is -> |%s|\n", ctr, argv[ctr]); 
		/* ex., argv[0] == the name of the program */ 
	} 
	
	return 0;
} 
