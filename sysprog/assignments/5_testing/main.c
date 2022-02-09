#include "presettings.h"

#include <math.h>
#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>
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

void reverse_big_integer_data(BigInteger *bigint) {
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


	reverse_big_integer_data(bigint);

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
	fputs("\t", stdout);

	for (size_t i = bigint->length; i > 0; i--) {
		printf("%d ", bigint->data[i - 1]);
	}

	putchar('\n');
}

// Calculate src + dest and store it in dest. Completely ignores the negative flag.
error_t add_big_integers(BigInteger *src, BigInteger *dest) {
	const size_t max_length = (
		src->length > dest->length ? src->length : dest->length
	);

	int carry = 0;

	for (size_t i = 0; i < max_length; i++) {
		// It's fine if we technically go over one of the bigints lengths
		// here because the buffers are zero-initialized

		// Sum is in [0, 19]
		const int sum = src->data[i] + dest->data[i] + carry;

		// Carry is either 0 or 1
		carry = sum / 10;
		// Final digit is in [0, 9]
		dest->data[i] = sum % 10;

		// If we made a contentful calculation just now...
		if (dest->data[i]) {
			dest->length = i + 1;
		}
	}

	// If we still have a leftover carry...
	if (carry) {
		// Make sure it will fit
		if (dest->length == MAX_LENGTH) {
			return EXIT_NUMBER_TOO_BIG;
		}

		dest->data[dest->length++] = carry;
	}

	return EXIT_OK;
}

// Returns a copy of a given biginteger, scaled by a value in [0, 9]. Caller is 
// responsible for freeing the created bigint in all cases.
BigInteger *scale_big_integer(BigInteger *src, char scale, error_t *error) {
	BigInteger *dest = create_big_integer("0", error);

	if (*error != EXIT_OK || scale == 0) {
		return dest;
	}

	// This is not particularly efficient but adds at most a constant factor
	// to the runtime so it'll be fine
	for (char i = 0; i < scale; i++) {
		error_t temp_error = EXIT_OK;

		if ((temp_error = add_big_integers(src, dest)) != EXIT_OK) {
			*error = temp_error;

			return dest;
		}
	}

	return dest;
}

// Returns a new bigintiger containing the result of a * b. Caller is resposible for 
// freeing the created bigint in all cases.
BigInteger *multiply_big_integers(BigInteger *a, BigInteger *b, error_t *error) {
	BigInteger *dest = create_big_integer("0", error);

	if (*error != EXIT_OK) {
		return dest;
	}

	for (size_t i = 0; i < a->length; i++) {
		
	}
}

// --- TESTING CODE ---

int big_integers_compare(BigInteger *a, BigInteger *b, bool absolute) {
	if (a->length > b->length) {
		return ((absolute || !a->negative) ? 1 : -1);
	} else if (a->length < b->length) {
		return ((absolute || !b->negative) ? -1 : 1);
	}

	// We know a->length == b->length

	if (!absolute) {
		if (!a->negative && b->negative) {
			return 1;
		} else if (a->negative && !b->negative) {
			return -1;
		}
	}

	for (size_t i = 0; i < a->length; i++) {
		if (a->data[i] > b->data[i]) {
			return (absolute || !a->negative) ? 1 : -1;
		} else if (a->data[i] < b->data[i]) {
			return (absolute || !a->negative) ? -1 : 1;
		}
	}

	return 0;
}

void test_big_integer_add(char *a, char *b, char *expected) {
	error_t error = EXIT_OK;

	BigInteger *ba = create_big_integer(a, &error);
	BigInteger *bb = create_big_integer(b, &error);
	BigInteger *bexpected = create_big_integer(expected, &error);

	assert(error == EXIT_OK);

	add_big_integers(ba, bb);

	assert(big_integers_compare(bb, bexpected, true) == 0);

	destroy_big_integer(ba);
	destroy_big_integer(bb);
	destroy_big_integer(bexpected);
}

void test_big_integer_scale(char *a, char scale, char *expected) {
	error_t error = EXIT_OK;

	BigInteger *ba = create_big_integer(a, &error);
	BigInteger *bexpected = create_big_integer(expected, &error);

	assert(error == EXIT_OK);

	BigInteger *scaled = scale_big_integer(ba, scale, &error);

	assert(error == EXIT_OK);

	assert(big_integers_compare(scaled, bexpected, true) == 0);

	destroy_big_integer(ba);
	destroy_big_integer(scaled);
	destroy_big_integer(bexpected);
}

void addition_test() {
	test_big_integer_add("0", "3", "3");
	test_big_integer_add("0", "100", "100");
	test_big_integer_add("100", "0", "100");
	test_big_integer_add("243872374", "123478324", "367350698");
}

void scale_test() {
	test_big_integer_scale("21322193872183123", 0, "0");
	test_big_integer_scale("5", 1, "5");
	test_big_integer_scale("9", 3, "27");
	test_big_integer_scale("99", 9, "891");
}

int main() {
	addition_test();

	scale_test();

	return 0;
}
