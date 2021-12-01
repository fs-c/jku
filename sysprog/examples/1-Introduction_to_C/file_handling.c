#include <stdio.h>
#include <stdlib.h>

int main(void) 
{ 
	/* file handles */ 
	FILE *output_file = NULL; 

	/* open files for writing*/ 
	output_file = fopen("out.dat", "w"); 
	/* need to do explicit ERROR CHECKING */ 
	if (output_file == NULL) 
		exit(1); 

	/* write some data into the file */ 
	fprintf(output_file, "Hello there"); 

	/* don't forget to close file handles */ 
	fclose(output_file); 
	
	return 0;
} 
