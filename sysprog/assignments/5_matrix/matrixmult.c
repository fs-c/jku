#include "presettings.h"

#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

typedef struct BigInteger {
	size_t length;
	bool negative;

	char *data;
} BigInteger;

typedef struct Matrix {
	size_t rows;
	size_t columns;

	// data[row][col]
	BigInteger ***data;
} Matrix;

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

// Creates a BigInteger struct from a string.
BigInteger *create_big_integer(char *raw_integer, error_t *err) {
	// Use calloc to make fields default to zero
	BigInteger *bigint = calloc(1, sizeof(BigInteger));

	if (!bigint) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	bigint->data = malloc(MAX_LENGTH);

	if (!bigint->data) {
		destroy_big_integer(bigint);

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
			destroy_big_integer(bigint);

			*err = EXIT_INVALID_NUMBER;

			return NULL;
		}

		bigint->data[i++] = c - '0';
	}

	bigint->length = i;

	if (!bigint->length) {
		destroy_big_integer(bigint);

		*err = EXIT_INVALID_NUMBER;

		return NULL;
	}

	bigint->data = realloc(bigint->data, bigint->length);

	if (!bigint->data) {
		destroy_big_integer(bigint);

		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	return bigint;
}

// Calculate x + y. UNUSED.
BigInteger *add_big_integers(BigInteger *x, BigInteger *y, error_t *error) {
	const size_t max_length = MAX_LENGTH + 1;
	char *raw_result = malloc(max_length);

	raw_result[max_length - 1] = '\0';

	BigInteger *larger = x->length > y->length ? x : y;

	char carry = 0;
	size_t i = 0;
	// Plus one for a potential carry after the last addition
	for (; i < larger->length + 1; i++) {
		char a = i >= x->length ? 0 : x->data[x->length - i];
		char b = i >= y->length ? 0 : y->data[y->length - i];

		char sum = a + b + carry;
		carry = sum / 10;
		sum %= 10;

		raw_result[max_length - 2 - i] = sum;
	}

	// Make sure that the carry didn't make us go over the length limit
	if (carry && larger->length == MAX_LENGTH) {
		*error = EXIT_NUMBER_TOO_BIG;

		free(raw_result);

		return NULL;
	}

	BigInteger *result = create_big_integer(raw_result + (max_length - 1 - i),
		error);

	free(raw_result);

	return result;
}

// Add src to dest in-place.
error_t add_to_big_integer(BigInteger *src, BigInteger *dest) {
	const size_t max_length = MAX_LENGTH + 1;

	BigInteger *larger = src->length > dest->length ? src : dest;

	char carry = 0;
	size_t i = 0;
	// Plus one for a potential carry after the last addition
	for (; i < larger->length + 1; i++) {
		char a = i >= src->length ? 0 : src->data[src->length - i];
		char b = i >= dest->length ? 0 : dest->data[dest->length - i];

		char sum = a + b + carry;
		carry = sum / 10;
		sum %= 10;

		

		raw_result[max_length - 2 - i] = sum;
	}

	// Make sure that the carry didn't make us go over the length limit
	if (carry && larger->length == MAX_LENGTH) {
		*error = EXIT_NUMBER_TOO_BIG;

		free(raw_result);

		return NULL;
	}

	BigInteger *result = create_big_integer(raw_result + (max_length - 1 - i),
		error);

	free(raw_result);

	return result;
}

// Calculate x * y where y is an int.
BigInteger *scale_big_integer(BigInteger *x, int y, error_t *error) {

}

// Calculate x * y.
BigInteger *multiply_big_integer(BigInteger *x, BigInteger *y, error_t *error) {
	BigInteger *result = create_big_integer("0", error);

	if (*error != EXIT_OK) {}

	BigInteger *larger = x->length > y->length ? x : y;
	BigInteger *smaller = x->length > y->length ? y : x;

	for (size_t i = 0; i < smaller->length; i++) {
		char factor = smaller->data[i];

		BigInteger *scaled = scale_big_integer(larger, factor * (i * 10),
			error);

		if (*error != EXIT_OK) {}

		add_to_big_integer(scaled, result);

		destroy_big_integer(scaled);
	}

	return result;
}

// Creates an empty matrix (2d array) of the given size. Might still return a 
// pointer to an incomplete matrix if *err is EXIT_OUT_OF_MEM, make sure to 
// destroy it. Doesn't initialize matrix data items.
Matrix *create_matrix(size_t rows, size_t columns, error_t *err) {
	// Make sure to always use calloc here, otherwise destroy_matrix might 
	// run into garbage values when called immediately after a partially failed
	// run of create_matrix. (In other cases the unitialized memory will always 
	// be overwritten anyways so it really only matters for destroy_matrix.)

	Matrix *matrix = calloc(1, sizeof(Matrix));

	if (!matrix) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	matrix->rows = rows;
	matrix->columns = columns;

	matrix->data = calloc(rows, sizeof(BigInteger **));

	if (!matrix) {
		*err = EXIT_OUT_OF_MEM;

		return matrix;
	}

	for (size_t row = 0; row < rows; row++) {
		matrix->data[row] = calloc(columns, sizeof(BigInteger *));

		if (!matrix->data[row]) {
			*err = EXIT_OUT_OF_MEM;

			return matrix;
		}
	}

	return matrix;
}

// Counterpart to create_matrix. Can also destroy matrices that were only partially
// allocated and will destroy any BigIntegers.
void destroy_matrix(Matrix *matrix) {
	if (!matrix) {
		return;
	}

	if (matrix->data) {
		for (size_t row = 0; row < matrix->rows; row++) {
			if (!matrix->data[row]) {
				continue;
			}

			for (size_t col = 0; col < matrix->columns; col++) {
				if (!matrix->data[row][col]) {
					continue;
				}

				destroy_big_integer(matrix->data[row][col]);
			}

			free(matrix->data[row]);
		}

		free(matrix->data);
	}

	free(matrix);
}

// Read and discard characters until a non-isspace() character is read. That
// character will be the first character on the stream after the call.
void skip_space(FILE *input_file) {
	char c;

	// Skip space characters and newlines etc.
	while (isspace(c = fgetc(input_file)))
		;

	// `c` isn't a space so add it to the front again
	ungetc(c, input_file);
}

// Read a word, i. e. a sequence of characters which are !isspace() until the first
// isspace() character is read. That character will be the first character on the
// stream after the call.
error_t read_word(FILE *input_file, char *word, size_t max_length) {
	skip_space(input_file);

	char c;
	size_t i = 0;

	while ((c = fgetc(input_file))) {
		if (isspace(c)) {
			break;
		}

		if (i >= (max_length - 1)) {
			return EXIT_NUMBER_TOO_BIG;
		}

		word[i++] = c;
	}

	ungetc(c, input_file);

	word[i] = '\0';

	return EXIT_OK;
}

int32_t read_int32(FILE *input_file, error_t *error) {
	// Maximum amount of digits for int32 is 10, plus one for \0
	const size_t max_length = 11;

	char *word = malloc(max_length);
	if ((*error = read_word(input_file, word, max_length)) != EXIT_OK) {
		free(word);

		return 0;
	}

	int32_t value = strtol(word, NULL, 10);

	free(word);

	return value;
}

void parse_matrix_block(FILE *input_file, Matrix *m, error_t *error) {
	const size_t max_length = MAX_LENGTH + 1;
	char *raw_integer = malloc(max_length);

	for (size_t row = 0; row < m->rows; row++) {
		for (size_t col = 0; col < m->columns; col++) {
			if (feof(input_file)) {
				free(raw_integer);

				*error = EXIT_INVALID_MATRIX;

				return;
			}

			if ((*error = read_word(input_file, raw_integer, max_length)) != EXIT_OK) {
				free(raw_integer);

				return;
			}

			m->data[row][col] = create_big_integer(raw_integer, error);

			if (*error != EXIT_OK) {
				free(raw_integer);

				return;
			}
		}
	}

	free(raw_integer);
}

void initialize_matrix(FILE *input_file, Matrix **m, error_t *error) {
	size_t rows = read_int32(input_file, error);
	size_t cols = read_int32(input_file, error);

	if (*error) {
		return;
	} else if (!rows || !cols) {
		*error = EXIT_INVALID_NUMBER;

		return ;
	}

	*m = create_matrix(rows, cols, error);
}

error_t parse_input_file(FILE *input_file, Matrix **m1, Matrix **m2) {
	error_t error = EXIT_OK;

	initialize_matrix(input_file, m1, &error);
	initialize_matrix(input_file, m2, &error);

	if (error != EXIT_OK) {
		return error;
	}

	if (!*m1 || !*m2) {
		return EXIT_INTERNAL;
	}

	if ((*m1)->columns != (*m2)->rows) {
		return EXIT_INCOMPATIBLE_DIM;
	}

	parse_matrix_block(input_file, *m1, &error);
	parse_matrix_block(input_file, *m2, &error);

	skip_space(input_file);

	if (!feof(input_file)) {
		return EXIT_INVALID_MATRIX;
	}

	return error;
}

void print_matrix(Matrix *m) {
	printf("matrix @ %p\n", m);

	if (!m) {
		return;
	}

	char num[MAX_LENGTH + 1];

	printf("\trows = %ld\n", m->rows);
	printf("\tcolumns = %ld\n", m->columns);
	printf("\tdata = %p\n", m->data);

	if (!m->data) {
		return;
	}

	for (size_t row = 0; row < m->rows; row++) {
		if (!m->data[row]) {
			continue;
		}

		for (size_t col = 0; col < m->columns; col++) {
			BigInteger *bigint = m->data[row][col];

			if (!bigint) {
				fputs("\tnull ", stdout);

				continue;
			}

			size_t i;
			for (i = 0; i < bigint->length; i++) {
				num[i] = bigint->data[i] + '0';
			}

			num[bigint->length] = '\0';

			putchar('\t');
			if (bigint->negative) {
				putchar('-');
			}
			fputs(num, stdout);
			putchar(' ');
		}

		putchar('\n');
	}

	putchar('\n');
}

int main(int argc, char *argv[]) {
	error_t error = EXIT_OK;

	if (argc != 2) {
		fputs(invalid_arg_num_str, stderr);

		return EXIT_ARGS;
	}

	char *input_file_name = argv[1];
	FILE *input_file = fopen(input_file_name, "r");

	if (!input_file) {
		fprintf(stderr, open_infile_err_str, input_file_name);

		return EXIT_IO;
	}

	Matrix *m1 = NULL, *m2 = NULL;

	if ((error = parse_input_file(input_file, &m1, &m2)) != EXIT_OK) {
		if (error == EXIT_OUT_OF_MEM) {
			fputs(out_of_mem_str, stderr);
		} else if (error == EXIT_NUMBER_TOO_BIG) {
			fprintf(stderr, number_too_big_str, MAX_LENGTH);
		} else {
			// Should be a dead code path
			fprintf(stderr, unknown_error_str, error);
		}

		// This is C after all
		goto cleanup;
	}

cleanup:
	print_matrix(m1);
	print_matrix(m2);

	destroy_matrix(m1);
	destroy_matrix(m2);

	if (fclose(input_file)) {
		fputs(close_file_err_str, stderr);

		return EXIT_IO;
	}

	return error;
}
