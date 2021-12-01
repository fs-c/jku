#include <stdio.h>
#include <stdlib.h>

/*
 * Demonstration of the 'qsort' and 'bsearch' library functions.
 */

int compare_ints(const void *p1, const void *p2);
void print_array(int numbers[], size_t length);
void search_int(int numbers[], size_t length, int to_search);

int main(void) { 
	int numbers[] = { 9, 2, 6, 3, 7, 0, -1, 5, 100 };
	
	/* Common idiom in C for getting the number of elements */
	size_t length = sizeof(numbers) / sizeof(numbers[0]);
	
	/* Print initial content of array */
	printf("Unsorted: ");
	print_array(numbers, length);
	printf("\n");
	
	/* Sort array 'in place' = the array is modified */
	qsort(numbers, length, sizeof(int), compare_ints);
	
	/* Print sorted array */
	printf("\nSorted: ");
	print_array(numbers, length);
	printf("\n");
	
	/* Search some elements through a helper function */
	search_int(numbers, length, 5);
	search_int(numbers, length, -1);
	search_int(numbers, length, 100);
	search_int(numbers, length, 20);
	
	return 0;
}

/* Comparison function used by 'qsort' and 'bsearch' */
int compare_ints(const void *p1, const void *p2) {

	/* Cast pointers to elements to correct type and fetch values */
	int nr1 = *((int *) p1);
	int nr2 = *((int *) p2);
	
	/* Informational message to show the individual search operations */
	printf("Comparing %d with %d\n", nr1, nr2);
	
	/* Returns a value < 0 if n1 < n2, 0 if n1 == n2 and a value > 0 if n1 > n2 */
	return nr1 - nr2;
}

/* Helper function for printing the contents of an integer array */
void print_array(int numbers[], size_t length) {
	size_t i;
	for (i = 0; i < length; i++) {
		printf("%d ", numbers[i]);
	}
	printf("\n");
}

/* Helper function for searching an element in an integer array */
void search_int(int numbers[], size_t length, int to_search) {

	/* Perform actual binary search */
	int *found = bsearch(&to_search, numbers, length, sizeof(int), compare_ints);
	
	/* Tell user if the element was found */
	if (found == NULL) {
		printf("Element %d not found in array\n", to_search);
	} else {
	
		/* Index is calculated through pointer arithmetic by subtracting the base address */
		printf("Element %d found at index %lu\n", to_search, found - numbers);
	}
}