#include <stdio.h> 

void init_array(int array[], int size); 

int main(void) 
{ 
	int j, list[5]; 
	init_array(list, 5); 

	for (j = 0; j < 5; j++) 
		printf("next:%d\n", list[j]); 
		
	return 0;
} 

void init_array(int array[], int size)  /* why size ? */ 
{
	/* arrays ALWAYS passed by reference */ 
	int i; 
	for (i = 0; i < size; i++) 
		array[i] = 0; 
} 
