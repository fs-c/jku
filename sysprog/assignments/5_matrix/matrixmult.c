#include "presettings.h"

#define __STDC_WANT_LIB_EXT2__ 1

#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct BigInteger {
	size_t length;

	char *data;
} BigInteger;

typedef struct Matrix {
	size_t rows;
	size_t columns;

	// data[column][row]
	BigInteger ***data;
} Matrix;

// Stub
BigInteger *create_big_integer(char *raw_integer, error_t *err) {
	BigInteger *bigint = malloc(sizeof(BigInteger));

	if (!bigint) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	while (*raw_integer) {
		

		raw_integer++;
	}

	return bigint;
}

// Stub?
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

	matrix->data = calloc(columns, sizeof(BigInteger **));

	if (!matrix) {
		*err = EXIT_OUT_OF_MEM;

		return matrix;
	}

	for (size_t column = 0; column < columns; column++) {
		matrix->data[column] = calloc(rows, sizeof(BigInteger *));

		if (!matrix->data[column]) {
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
		for (size_t column = 0; column < matrix->columns; column++) {
			if (!matrix->data[column]) {
				continue;
			}

			for (size_t row = 0; row < matrix->rows; row++) {
				if (!matrix->data[column][row]) {
					continue;
				}

				destroy_big_integer(matrix->data[column][row]);
			}

			free(matrix->data[column]);
		}

		free(matrix->data);
	}

	free(matrix);
}

// Parses the 'header line' of input files.
error_t parse_first_line(char *line, int *n, int *m, int *p, int *q) {
	for (int i = 0; i < 4; i++) {
		// strtol sets end to the position it last read from + 1
		char *end;
		const long value = strtol(line, &end, 10);

		line = end;

		switch (i) {
			case 0: *n = value;
				break;
			case 1: *m = value;
				break;
			case 2: *p = value;
				break;
			case 3: *q = value;
				break;
		}
	}

	return EXIT_OK;
}

// Reads characters from `*file` until it encounters a non-space character. The
// `pure` parameter determines how space is defined, if true it is ' ', otherwise 
// is is isspace().
void skip_space_stream(FILE *file) {

}

char *skip_space_string(char *string) {
	while (*string && (isspace(*string++)))
		;

	return string;
}

// 94289238429424239847203984092 928409238432    	242398423  132948209384 888
error_t parse_matrix_row(char *line, Matrix *m) {
	char *raw_value = malloc(MAX_LENGTH + 1);

	char *temp = line;
	while ((temp = skip_space_string(temp)) != line) {
		line = temp;

		size_t i;
		for (i = 0; i < MAX_LENGTH; i++) {
			if (isspace(line[i])) {
				break;
			}

			raw_value[i] = *line++;
		}

		if (!isspace(*line)) {
			free(raw_value);

			return EXIT_NUMBER_TOO_BIG;
		}

		raw_value[i + 1] = '\0';
	}
}

error_t parse_matrix_data(FILE *input_file, Matrix *m) {
	skip_space_stream(input_file);

	char *line = malloc(MAX_LINE_LENGTH);

	for (size_t row = 0; row < m->rows; row++) {
		if (!fgets(line, MAX_LINE_LENGTH, input_file)) {
			free(line);

			return EXIT_IO;
		}

		parse_matrix_row(line, m);

		skip_space_stream(input_file);
	}

	free(line);

	return EXIT_OK;
}

// Make sure to destroy m1 and m2 even if an error occurred.
error_t read_input_file(FILE *input_file, Matrix **m1, Matrix **m2) {
	error_t error = EXIT_OK;
	char *line_buffer = malloc(MAX_LINE_LENGTH);

	if (!line_buffer) {
		return EXIT_OUT_OF_MEM;
	}

	// Read first line
	if (!fgets(line_buffer, MAX_LINE_LENGTH, input_file)) {
		free(line_buffer);

		return EXIT_IO;
	}

	// Parse first line
	int n, m, p, q;
	if ((error = parse_first_line(line_buffer, &n, &m, &p, &q)) != EXIT_OK) {
		free(line_buffer);

		return error;
	}

	// Check that cols of first matrix = rows of second matrix
	if (n != p) {
		free(line_buffer);

		return EXIT_INCOMPATIBLE_DIM;
	}

	*m1 = create_matrix(n, m, &error);
	*m2 = create_matrix(p, q, &error);

	if (error != EXIT_OK) {
		free(line_buffer);

		return error;
	}

	parse_matrix_data(input_file, *m1);
	parse_matrix_data(input_file, *m2);

	free(line_buffer);

	return error;
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

	if ((error = read_input_file(input_file, &m1, &m2)) != EXIT_OK) {
		if (error == EXIT_IO) {
			fputs(in_out_error_str, stderr);
		} else if (error == EXIT_OUT_OF_MEM) {
			fputs(out_of_mem_str, stderr);
		} else if (error == EXIT_INVALID_MATRIX) {
			fputs(invalid_matrix_str, stderr);
		}

		return error;
	}

	destroy_matrix(m1);
	destroy_matrix(m2);

	if (fclose(input_file)) {
		fputs(close_file_err_str, stderr);

		return EXIT_IO;
	}

	return error;
}
