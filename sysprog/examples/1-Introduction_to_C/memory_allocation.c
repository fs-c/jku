#include <stdio.h> 
#include <stdlib.h>

int main(void) 
{ 
	int *ptr; 

	/* allocate space to hold an int */ 
	ptr = (int*)malloc(sizeof(int)); 

	/* check if we got memory */
	if(ptr==NULL)
		return -1;

	/* do stuff with the space */ 
	*ptr=4; 

	 /* free up the allocated space */
	free(ptr); 
	
	return 0;
} 
