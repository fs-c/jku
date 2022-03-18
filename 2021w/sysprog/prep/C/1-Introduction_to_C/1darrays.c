#include <stdio.h> 

int main(void) { 

	int number[12]; /* 12 cells, one cell per student */ 
	int index, sum = 0; 

	/* Always initialize array before use */ 
	for (index = 0; index < 12; index++) { 
		number[index] = index; 
	} 
	/* now, number[index]=index; will cause error: why ?*/ 

	for (index = 0; index < 12; index = index + 1) { 
		sum += number[index]; /* sum array elements */ 
	} 

	printf("sum: %d\n", sum); 
	
	return 0;
} 
