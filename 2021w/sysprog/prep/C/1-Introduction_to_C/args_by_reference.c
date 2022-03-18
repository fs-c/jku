#include <stdio.h> 

/* function prototype at start of file */ 
int sum(int *pa, int *pb); 

int main(void) 
{ 
	int a=4, b=5; 
	int *ptr = &b; 
	int total = sum(&a,ptr); /* call to the function */ 
	printf("The sum of 4 and 5 is %d", total); 
	
	return 0;
} 

/* the function itself - arguments passed by reference */ 
int sum(int *pa, int *pb) { 
	return (*pa + *pb); /* return by value */ 
} 
