#include "presettings.h"

#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <assert.h>

typedef struct BigInteger {
	size_t length;
	bool negative;

	// An array of digits (0 - 9)
	char *data;
} BigInteger;

// Counterpart to create_big_integer. Destroys a BigInteger struct.
void destroy_big_integer(BigInteger *bigint) {
	if (!bigint) {
		return;
	}

	if (bigint->data) {
		free(bigint->data);
	}

	free(bigint);

	return;
}

void reverse_big_integer(BigInteger *bigint) {
	for (size_t i = 0; i < bigint->length / 2; i++) {
		size_t reverse_i = bigint->length - 1 - i;
		char temp = bigint->data[reverse_i];

		bigint->data[reverse_i] = bigint->data[i];
		bigint->data[i] = temp;
	}
}

// Creates a BigInteger struct from a string. Guarantees that digits are zeroed.
// The data in the struct will be in reverse. E. g. "123" -> [ 3, 2, 1 ].
BigInteger *create_big_integer(char *raw_integer, error_t *err) {
	// Use calloc to make fields default to zero
	BigInteger *bigint = calloc(1, sizeof(BigInteger));

	if (!bigint) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	// Make sure that unset digits are zeroed
	bigint->data = calloc(1, MAX_LENGTH);

	if (!bigint->data) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	if (*raw_integer == '-') {
		bigint->negative = true;
		raw_integer++;
	}

	char c;
	size_t i = 0;
	while ((c = *raw_integer++)) {
		if (!isdigit(c) || i >= MAX_LENGTH) {
			*err = EXIT_INVALID_NUMBER;

			return NULL;
		}

		bigint->data[i++] = c - '0';
	}

	bigint->length = i;

	if (!bigint->length) {
		*err = EXIT_INVALID_NUMBER;

		return NULL;
	}


	reverse_big_integer(bigint);

	return bigint;
}

void print_big_integer(BigInteger *bigint) {
	printf("\nbigint @ %p\n", bigint);

	if (!bigint) {
		return;
	}

	printf("\tlength = %ld\n", bigint->length);
	printf("\tnegative = %d\n", bigint->negative);

	putchar('\n');
	putchar('\t');

	for (size_t i = 0; i < bigint->length; i++) {
		printf("%d ", bigint->data[i]);
	}

	putchar('\n');
	putchar('\t');

	for (size_t i = bigint->length; i > 0; i--) {
		printf("%d ", bigint->data[i - 1]);
	}

	putchar('\n');
}

int main() {
	error_t error = EXIT_OK;

	BigInteger *a = create_big_integer("868384567", &error);
	BigInteger *b = create_big_integer("-97", &error);
	BigInteger *c = create_big_integer("31", &error);
	BigInteger *d = create_big_integer("2", &error);

	if (error != EXIT_OK) {
		destroy_big_integer(a);
		destroy_big_integer(b);
		destroy_big_integer(c);
		destroy_big_integer(d);

		printf("error: %d\n", error);

		return 1;
	}

	print_big_integer(a);
	print_big_integer(b);
	print_big_integer(c);
	print_big_integer(d);

	assert(a->length == 9);
	assert(b->length == 2);
	assert(c->length == 2);
	assert(d->length == 1);

	destroy_big_integer(a);
	destroy_big_integer(b);
	destroy_big_integer(c);
	destroy_big_integer(d);

	putchar('\n');

	return 0;
}
