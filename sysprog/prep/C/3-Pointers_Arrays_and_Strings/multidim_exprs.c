#include <stdio.h>

void print_header(void) {
	printf("\n");
	printf(" expression \t\t   value of result   size of type \t type\n");
	printf("--------------------------------------------------------------------------\n");
}

int main(void) { 
	
	int multi[5][10] = {{ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9},
						{10, 11, 12, 13, 14, 15, 16, 17, 18, 19},
						{20, 21, 22, 23, 24, 25, 26, 27, 28, 29},
						{30, 31, 32, 33, 34, 35, 36, 37, 38, 39},
						{40, 41, 42, 43, 44, 45, 46, 47, 48, 49}};

	printf("\n");
	printf("\tThese expressions all return a pointer to the same spot\n");
	printf("\tin memory, but the type of their result is different.\n");
	print_header();
	
	printf(" multi[0] \t\t= %15p \t %6lu \t int[10]\n", multi[0], sizeof(multi[0]));
	printf(" &multi[0] \t\t= %15p \t %6lu \t address of int[10]\n", &multi[0], sizeof(&multi[0]));
	printf(" multi \t\t\t= %15p \t %6lu \t int[5][10]\n", multi, sizeof(multi));
	printf(" *multi \t\t= %15p \t %6lu \t int[10]\n", *multi, sizeof(*multi));
	
	printf("\n");
	printf("\tArray indexing notation and pointer arithmetic with the array's\n");
	printf("\tbase address (plus dereferencing) lead to the same result.\n");
	print_header();
	
	printf(" multi[1] \t\t= %15p \t %6lu \t int[10]\n", multi[1], sizeof(multi[1]));
	printf(" multi + 1 \t\t= %15p \t %6lu \t address of int[10]\n", multi + 1, sizeof(multi + 1));
	printf(" *(multi + 1) \t\t= %15p \t %6lu \t int[10]\n", *(multi + 1), sizeof(*(multi + 1)));
	
	printf("\n");
	printf("\tThis again shows the equivalence of these two notations. The \n");
	printf("\tbase address of a 2-dimensional array can be thought of as a \n");
	printf("\tpointer to pointers. Hence the need for dereferencing twice.\n");
	print_header();
	
	printf(" multi[3][1] \t\t= %15d \t %6lu \t int\n", multi[3][1], sizeof(multi[3][1]));
	printf(" *(multi + 3) + 1 \t= %15p \t %6lu \t int*\n", *(multi + 3) + 1, sizeof(*(multi + 3) + 1));
	printf(" *(*(multi + 3) + 1) \t= %15d \t %6lu \t int\n", *(*(multi + 3) + 1), sizeof(*(*(multi + 3) + 1)));
	printf(" &multi[3][1] \t\t= %15p \t %6lu \t int*\n", &multi[3][1], sizeof(&multi[3][1]));
	
	printf("\n");
	printf("\tCompare these results to the results of multi[0] and multi[1] to\n");
	printf("\tsee that the first elements of a row start at the base of the row.\n");
	print_header();
	
	printf(" &multi[0][0] \t\t= %15p \t %6lu \t int*\n", &multi[0][0], sizeof(&multi[0][0]));
	printf(" &multi[1][0] \t\t= %15p \t %6lu \t int*\n", &multi[1][0], sizeof(&multi[1][0]));
	printf("\n");
	
	return 0;
} 
