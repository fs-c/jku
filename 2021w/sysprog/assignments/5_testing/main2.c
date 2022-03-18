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
	fputs("\t", stdout);

	for (size_t i = bigint->length; i > 0; i--) {
		printf("%d ", bigint->data[i - 1]);
	}

	putchar('\n');
}

// Returns 0 if a == b, -1 if a < b, 1 if a > b
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

/*

- 6
  4
- 2

 23 3-9 = -6, absolute diff to -10, carry -1
-19
 04

 09 9-1 = 8, carry 1, absolute diff to 10
-11
-02

  23489234 a	if abs(b) < abs(a), absolute diff to 10, carry +1
- 94829388 b	IF ABS(A) < ABS(B)
  71340154

  94829388 a	if abs(b) > abs(a), absolute diff to -10, carry -1
- 23489234 b	IF ABS(A) > ABS(B)
  71340154

    8423984 a
- 238420983 b
- 229996999

  238420983 a
-   8423984 b
  229996999

*/

error_t add_big_integers(BigInteger *src, BigInteger *dest) {
	const size_t max_length = (
		src->length > dest->length ? src->length : dest->length
	);

	const bool both_negative = src->negative && dest->negative;
	// Don't do a regular subtraction if both are negative, just add normally
	const bool subtracting = !both_negative && (src->negative || dest->negative);

	const short src_factor = (src->negative && !both_negative) ? -1 : 1;
	const short dest_factor = (dest->negative && !both_negative) ? -1 : 1;

	const int comparison = big_integers_compare(src, dest, true);
	const bool negative_smaller = subtracting ? (
		src->negative ? comparison == 1 : comparison == -1
	) : false;

	// Set up defaults for result (length defaults to one, i. e. one zero)
	dest->length = 1;
	dest->negative = false;

	if (!comparison && subtracting) {
		memset(dest->data, 0, MAX_LENGTH);

		return EXIT_OK;
	}

	int carry = 0;

	// Iterate to max_length + 1 in case we have a carry at the end
	for (size_t i = 0; i < max_length + 1; i++) {
		// It's fine if we technically go over one of the bigints lengths
		// here because the buffers are zero-initialized
		const char a = src->data[i] * src_factor;
		const char b = dest->data[i] * dest_factor;

		// Looked easier in primary school tbh

		// [-18, 18]
		const int sum = a + b + carry;

		if (subtracting) {
			carry = negative_smaller
				? (sum > 0 ? 1 : 0)
				: (sum < 0 ? -1 : 0);

			dest->data[i] = negative_smaller
				? (sum > 0 ? abs(10 - sum) : abs(sum))
				: (sum < 0 ? abs(sum + 10) : abs(sum));
		} else {
			carry = sum / 10;
			dest->data[i] = sum % 10;
		}

		// If we made a contentful calculation just now...
		if (dest->data[i]) {
			dest->length = i + 1;

			if (subtracting) {
				dest->negative = sum < 0;
			}
		}
	}

	return EXIT_OK;
}

void length_test() {
	error_t error = EXIT_OK;

	BigInteger *a = create_big_integer("0", &error);
	BigInteger *b = create_big_integer("8683845673424", &error);

	if (error != EXIT_OK) {
		destroy_big_integer(a);
		destroy_big_integer(b);

		printf("error: %d\n", error);

		return;
	}

	assert(a->length == 1);
	assert(b->length == 13);

	destroy_big_integer(a);
	destroy_big_integer(b);
}

void test_big_integer_add(char *a, char *b, char *expected) {
	error_t error = EXIT_OK;

	BigInteger *ba = create_big_integer(a, &error);
	BigInteger *bb = create_big_integer(b, &error);
	BigInteger *bexpected = create_big_integer(expected, &error);

	assert(error == EXIT_OK);

	print_big_integer(ba);
	print_big_integer(bb);

	add_big_integers(ba, bb);

	print_big_integer(bb);

	assert(big_integers_compare(bb, bexpected, true) == 0);

	destroy_big_integer(ba);
	destroy_big_integer(bb);
	destroy_big_integer(bexpected);
}

void addition_test() {
	// Both operands positive
	test_big_integer_add("0", "3", "3");
	test_big_integer_add("3", "8", "11");
	test_big_integer_add("100000000000000000000000009", "1", "100000000000000000000000010");

	// Both operands negative
	test_big_integer_add("-4", "-6", "-10");
	test_big_integer_add("-100000000000000000000000009", "-1", "-100000000000000000000000010");

	// One operand negative

	// Stable length
	test_big_integer_add("4", "-6", "-2");
	test_big_integer_add("-6", "4", "-2");
	test_big_integer_add("-4", "0", "-4");
	test_big_integer_add("0", "-8", "-8");
	test_big_integer_add("100000000000000000000000009", "-7", "100000000000000000000000002");

	// Non-stable length
	test_big_integer_add("123456", "-123456", "0");
	test_big_integer_add("8423984", "-238420983", "-229996999");
	test_big_integer_add("238420983", "-8423984", "229996999");
	test_big_integer_add("5384753248783", "-4236428734236", "1148324514547");
}

void utils_test() {
	error_t error = EXIT_OK;

	BigInteger *a = create_big_integer("123456", &error);
	BigInteger *b = create_big_integer("-123456", &error);
	BigInteger *c = create_big_integer("77", &error);
	BigInteger *d = create_big_integer("4", &error);
	BigInteger *e = create_big_integer("-6", &error);

	assert(big_integers_compare(a, a, false) == 0);
	assert(big_integers_compare(a, b, false) == 1);
	assert(big_integers_compare(b, a, false) == -1);
	assert(big_integers_compare(b, a, true) == 0);
	assert(big_integers_compare(b, c, true) == 1);
	assert(big_integers_compare(c, b, true) == -1);
	assert(big_integers_compare(b, c, false) == -1);
	assert(big_integers_compare(d, e, false) == 1);
	assert(big_integers_compare(d, e, true) == -1);

	destroy_big_integer(a);
	destroy_big_integer(b);
	destroy_big_integer(c);
	destroy_big_integer(d);
	destroy_big_integer(e);
}

int main() {
	utils_test();

	length_test();

	addition_test();

	return 0;
}
