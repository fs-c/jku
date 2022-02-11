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

// Reverses the content of the data field of the given bigint.
void reverse_big_integer_data(BigInteger *bigint) {
	for (size_t i = 0; i < bigint->length / 2; i++) {
		size_t reverse_i = bigint->length - 1 - i;
		char temp = bigint->data[reverse_i];

		bigint->data[reverse_i] = bigint->data[i];
		bigint->data[i] = temp;
	}
}

// Parses a string containing a number into a bigint.
error_t parse_raw_integer(char *raw_integer, BigInteger *bigint) {
	char c;
	size_t i = 0;
	while ((c = *raw_integer++)) {
		if (!isdigit(c)) {
			return EXIT_INVALID_NUMBER;
		}

		if (i > MAX_LENGTH) {
			return EXIT_NUMBER_TOO_BIG;
		}

		bigint->data[i++] = c - '0';
	}

	bigint->length = i;

	if (!bigint->length) {
		return EXIT_INVALID_NUMBER;
	}

	return EXIT_OK;
}

// Creates a BigInteger struct from a string. Guarantees that digits are zeroed.
// The data in the struct will be reversed. E. g. "123" -> [ 3, 2, 1 ]. Caller
// is responsible for cleanup in all cases
BigInteger *create_big_integer(char *raw_integer, error_t *error) {
	// Use calloc to make fields (length, negative, ...) default to zero
	BigInteger *bigint = calloc(1, sizeof(BigInteger));

	if (!bigint) {
		*error = EXIT_OUT_OF_MEM;

		return NULL;
	}

	// Make sure that unset digits are zeroed
	bigint->data = calloc(1, MAX_LENGTH);

	if (!bigint->data) {
		*error = EXIT_OUT_OF_MEM;

		return bigint;
	}

	if (*raw_integer == '-') {
		bigint->negative = true;
		raw_integer++;
	}

	if ((*error = parse_raw_integer(raw_integer, bigint)) != EXIT_OK) {
		return bigint;
	}

	reverse_big_integer_data(bigint);

	return bigint;
}

// Analogous to strcmp, returns 0 if a == b, -1 if a < b and 1 if a > b. If 
// absolute is true, ignores the sign.
int compare_big_integers(BigInteger *a, BigInteger *b, bool absolute) {
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

// Calculate src + dest and stores it in dest. Exactly one of src or dest has to
// be negative.
error_t subtract_big_integers(BigInteger *src, BigInteger *dest) {
	const size_t max_length = (
		src->length > dest->length ? src->length : dest->length
	);

	bool swapped_sign = false;

	// Wrapping this in a scope because the variables would be potentially 
	// confusing otherwise
	{
		BigInteger *negative = src->negative ? src : dest;
		BigInteger *positive = negative == src ? dest : src;

		// If the negative value is larger than the positive one (in absolute terms)...
		if (compare_big_integers(negative, positive, true) > 0) {
			// Swap their signedness to make the naiive algorithm work
			negative->negative = false;
			positive->negative = true;

			swapped_sign = true;
		}
	}

	const int src_factor = src->negative ? -1 : 1;
	const int dest_factor = dest->negative ? -1 : 1;

	size_t i;
	int carry = 0;

	for (i = 0; i < max_length; i++) {
		const int sum = (src->data[i] * src_factor)
			+ (dest->data[i] * dest_factor) + carry;

		if (sum < 0) {
			carry = -1;
			dest->data[i] = sum + 10;
		} else {
			carry = 0;
			dest->data[i] = sum;
		}
	}

	dest->length = i;

	// We can never have a carry at this point because the negative value is 
	// guaranteed to be smaller than the positive one.

	if (swapped_sign) {
		// If we previously swapped the signs of the operands, make sure 
		// to change them back
		dest->negative = !dest->negative;
		src->negative = !src->negative;
	} else {
		// But if we didn't dest is sure to be positive right now
		dest->negative = false;
	}

	return EXIT_OK;
}

// Calculate src + dest and store it in dest. If absolute is true, ignores the sign.
error_t add_big_integers(BigInteger *src, BigInteger *dest, bool absolute) {
	// If either src or dest are zero, immediately return the other one
	if (src->length == 1 && !src->data[src->length - 1]) {
		// src is zero so dest remains unchanged
		return EXIT_OK;
	} else if (dest->length == 1 && !dest->data[dest->length - 1]) {
		// dest is zero so just copy src into it
		dest->length = src->length;
		dest->negative = absolute ? dest->negative : src->negative;

		memmove(dest->data, src->data, src->length);

		return EXIT_OK;
	}

	// If exactly one of the numbers is negative, perform a subtraction
	if (!absolute && (src->negative ^ dest->negative)) {
		return subtract_big_integers(src, dest);
	}

	// We know that either none or both of the numbers are negative now. If 
	// both are negative we can just perform addition as if none of them were.
	
	const size_t max_length = (
		src->length > dest->length ? src->length : dest->length
	);

	size_t i;
	int carry = 0;

	for (i = 0; i < max_length; i++) {
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
		if (i + 1 > MAX_LENGTH) {
			return EXIT_NUMBER_TOO_BIG;
		}

		dest->length = i + 1;
		dest->data[i] = carry;
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

		if ((temp_error = add_big_integers(src, dest, true)) != EXIT_OK) {
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
		BigInteger *scaled = scale_big_integer(b, a->data[i], error);

		if (*error != EXIT_OK) {
			destroy_big_integer(scaled);

			return dest;
		}

		if ((scaled->length + i) > MAX_LENGTH) {
			*error = EXIT_NUMBER_TOO_BIG;

			return dest;
		}

		// Multiply `scaled` by 10^i by adding i zeroes to the end
		memmove(scaled->data + i, scaled->data, scaled->length);
		memset(scaled->data, 0, i);
		scaled->length += i;

		error_t temp_error = EXIT_OK;

		if ((temp_error = add_big_integers(scaled, dest, true)) != EXIT_OK) {
			*error = temp_error;

			destroy_big_integer(scaled);

			return dest;
		}

		destroy_big_integer(scaled);
	}

	const bool one_negative = !(a->negative && b->negative)
		&& (a->negative || b->negative);

	if (one_negative) {
		dest->negative = true;
	}

	return dest;
}

// --- TESTING CODE ---

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

void print_big_integer_content(BigInteger *bigint) {
	if (bigint->negative) {
		putchar('-');
	}

	for (size_t i = bigint->length; i > 0; i--) {
		printf("%d", bigint->data[i - 1]);
	}
}

void test_big_integer_add(char *a, char *b, char *expected) {
	error_t error = EXIT_OK;

	BigInteger *ba = create_big_integer(a, &error);
	BigInteger *bb = create_big_integer(b, &error);
	BigInteger *bexpected = create_big_integer(expected, &error);

	assert(error == EXIT_OK);

	print_big_integer_content(ba);
	fputs(" + ", stdout);
	print_big_integer_content(bb);
	fputs(" = ", stdout);

	add_big_integers(ba, bb, false);

	print_big_integer_content(bexpected);

	putchar('\n');

	print_big_integer(bb);
	print_big_integer(bexpected);

	fflush(stdout);

	assert(compare_big_integers(bb, bexpected, false) == 0);

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

	assert(compare_big_integers(scaled, bexpected, true) == 0);

	destroy_big_integer(ba);
	destroy_big_integer(scaled);
	destroy_big_integer(bexpected);
}

void test_big_integer_multiply(char *a, char *b, char *expected) {
	error_t error = EXIT_OK;

	BigInteger *ba = create_big_integer(a, &error);
	BigInteger *bb = create_big_integer(b, &error);
	BigInteger *bexpected = create_big_integer(expected, &error);

	assert(error == EXIT_OK);

	print_big_integer_content(ba);
	fputs(" * ", stdout);
	print_big_integer_content(bb);
	fputs(" = ", stdout);
	BigInteger *result = multiply_big_integers(ba, bb, &error);

	print_big_integer_content(result);

	putchar('\n');
	fflush(stdout);

	assert(error == EXIT_OK);

	assert(compare_big_integers(result, bexpected, false) == 0);

	destroy_big_integer(ba);
	destroy_big_integer(bb);
	destroy_big_integer(bexpected);
	destroy_big_integer(result);
}

void addition_test() {
	test_big_integer_add("0", "3", "3");
	test_big_integer_add("0", "100", "100");
	test_big_integer_add("100", "0", "100");
	test_big_integer_add("123874", "123874", "247748");
	test_big_integer_add("243872374", "123478324", "367350698");
	test_big_integer_add("85674000", "16577919", "102251919");

	test_big_integer_add("0", "-19", "-19");
	test_big_integer_add("-19", "0", "-19");
	test_big_integer_add("134", "-19", "115");
	test_big_integer_add("8274374273", "-2183742", "8272190531");
	test_big_integer_add("-2183742", "8274374273", "8272190531");
}

void scale_test() {
	test_big_integer_scale("21322193872183123", 0, "0");
	test_big_integer_scale("5", 1, "5");
	test_big_integer_scale("9", 3, "27");
	test_big_integer_scale("99", 9, "891");
	test_big_integer_scale("99", 9, "891");
}

void multiplication_test() {
	test_big_integer_multiply("2", "0", "0");
	test_big_integer_multiply("0", "2", "0");
	test_big_integer_multiply("2", "4", "8");
	test_big_integer_multiply("20", "420", "8400");
	test_big_integer_multiply("1337", "123", "164451");
	test_big_integer_multiply("13370000000", "123", "1644510000000");
	test_big_integer_multiply("1425", "456", "649800");
	test_big_integer_multiply("42", "12387", "520254");
	test_big_integer_multiply("4283", "1233", "5280939");
	test_big_integer_multiply("42837", "12387", "530621919");
	test_big_integer_multiply("428374", "123874", "53064400876");
	test_big_integer_multiply("4283743", "123874", "530644380382");
	test_big_integer_multiply("-42837432", "-123874", "5306444051568");
	test_big_integer_multiply("-42837432", "123874", "-5306444051568");
}

int main() {
	scale_test();

	multiplication_test();

	addition_test();

	return 0;
}
