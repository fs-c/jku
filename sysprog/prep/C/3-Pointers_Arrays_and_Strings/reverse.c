#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* 
 * Reverses two strings:
 *  - by using array notation
 *  - by using pointer arithmetic 
 */

static void reverse_array(char[]);
static void reverse_pointer(char *);

int main(void) {

	/* First string */
	char string_in_array[] = "Hello World!";
	size_t length = sizeof(string_in_array);
	
	/* Allocate memory for second string */
	char *string_via_pointer = malloc(length * sizeof(char));
	if (string_via_pointer == NULL) {
		perror("Memory allocation failed");
		exit(EXIT_FAILURE);
	}
	
	/* Copy first string to second string */
	strncpy(string_via_pointer, string_in_array, length);
	
	/* Reverse first string */
	reverse_array(string_in_array);
	
	/* Print reversed string */
	if (string_in_array != NULL) {
		printf("First string: %s\n", string_in_array);
	}
	
	/* Reverse second string */
	reverse_pointer(string_via_pointer);
	
	/* Print reversed string */
	if (string_via_pointer != NULL) {
		printf("Second string: %s\n", string_via_pointer);
	}
	
	/* Free memory allocated for second string */
	free(string_via_pointer);
	
	return EXIT_SUCCESS;
}

/* 
 * Reverse string by using array notation 
 */
void reverse_array(char string[]) {
	size_t length = (size_t) 0u;
	unsigned int i = 0;
	char temp = ' ';
	
	if (string == NULL) {
		return;
	}
	
	length = strlen(string);
	
	/* Switch characters from start and end, moving towards the middle */
	for (i = 0; i < (length / 2); i++) {
		temp = string[i];
		string[i] = string[length - i - 1];
		string[length - i - 1] = temp;
	}
}

/* 
 * Reverse string by using pointer arithmetic 
 */
void reverse_pointer(char *string) {
	size_t length = (size_t) 0u;
	char temp = ' ', *left = NULL, *right = NULL;
	
	if (string == NULL) {
		return;
	}
	
	length = strlen(string);
	
	/* Start switching characters at beginning and end */
	left = string;
	right = string + length - 1;
	
	/* As long as pointers don't 'cross' */
	while(left < right) {
	
		/* Switch characaters */
		temp = *left;
		*left = *right;
		*right = temp;
		
		/* Advance pointers */
		left++;
		right--;
	}
}