#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {

	char s1[20] = "Hello";
	char *s2 = " World!";

	printf("String '%s' is %d characters long.\n", s1, (int) strlen(s1));

	/* Concatenating s1 and s2: contents of s2 are appended to s1 */
	strcat(s1, s2);
	printf("String '%s' is %d characters long.\n", s1, (int) strlen(s1));

	/* Concatenating a very long string */
	strncat(s1, " How are you?", sizeof(s1) - strlen(s1) - 1);	/* 1 space left for trailing \0 */
	printf("String '%s' is %d characters long.\n", s1, (int) strlen(s1));

	/* Copying a string appends a trailing \0 and 'ends' the string even if there are other characters afterwards */
	strcpy(s1, "Hallo");		/* DANGEROUS if s1 is too small */
	printf("String '%s' is %d characters long.\n", s1, (int) strlen(s1));

	/* Copying with size constraint */
	strncpy(s1, "Hallo Welt! Wie geht es dir?", sizeof(s1));	/* no \0 terminator written */
	s1[sizeof(s1) - 1] = '\0';
	printf("String '%s' is %d characters long.\n", s1, (int) strlen(s1));

	/* Duplicating a string (allocates new memory) */
	s2 = strdup(s1);
	printf("String '%s' is %d characters long.\n\n", s2, (int) strlen(s2));

	/* Free old space before re-using pointer for new string */
	free(s2);
	s2 = "Hallo Welt!";

	/* Compare strings */
	if (!strcmp(s1, s2)) {
		printf("Strings are equal.\n");
	} else {
		printf("Strings are NOT equal.\n");
	}

	/* Compare parts of strings */
	if (!strncmp(s1, s2, strlen(s2))) {
		printf("String s2 is prefix of s1.\n");
	} else {
		printf("Strings are NOT equal.\n");
	}
	printf("\n");

	// Find exclamation mark in string
	s2 = strchr(s1, '!');
	if (s2 != NULL) {
		printf("Exclamation mark is at index %ld and text afterwards is '%s'\n", (s2 - s1), s2 + 1);
	} else {
		fprintf(stderr, "Exclamation mark not found in string '%s'.\n", s1);
	}
	printf("\n");

	// Find 'Welt' in string
	char *s3 = "Welt";
	s2 = strstr(s1, s3);
	if (s2 != NULL) {
		printf("Sub-string '%s' is at index %ld and text afterwards is '%s'\n", s3, (s2 - s1), s2 + strlen(s3));
	} else {
		fprintf(stderr, "Sub-string '%s' not found in string '%s'.\n", s3, s1);
	}
	printf("\n");

	// Tokenize string (must be writable)
	char string[] = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nullam blandit velit purus, a ultrices quam.";
	char *delimiters = ",.";
	char *token = strtok(string, delimiters);
	int i = 1;

	while(token) {
		printf("Token: %s\n", token);
		token = strtok(NULL, delimiters);	// Get next token
		i++;

		// Change delimiters mid-way
		if (i == 2) {
			delimiters = " ";
		}
	}

	printf("\nOriginal string was changed to: ");
	for (i = 0; i < sizeof(string); ++i) {
		char c = string[i];
		if (c == '\0') {
			fputs("\\0", stdout);
		} else {
			putchar(c);
		}
	}
	printf("\n");

	return 0;
}
