#include "presettings.h"

#include <stdlib.h>

typedef struct Matrix {
	size_t rows;
	size_t columns;

	int **data;
} Matrix;

// Creates a matrix (2d array) of the given size. Might still return a pointer to 
// an incomplete matrix if *err is EXIT_OUT_OF_MEM, make sure to destroy it. 
Matrix *create_matrix(size_t rows, size_t columns, error_t *err) {
	Matrix *matrix = malloc(sizeof(Matrix));

	if (!matrix) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	matrix->rows = rows;
	matrix->columns = columns;

	matrix->data = malloc(rows * sizeof(int *));

	if (!matrix) {
		*err = EXIT_OUT_OF_MEM;

		return matrix;
	}

	for (size_t row = 0; row < rows; row++) {
		matrix->data[row] = malloc(columns * sizeof(int));

		if (!matrix->data[row]) {
			*err = EXIT_OUT_OF_MEM;

			return matrix;
		}
	}

	return matrix;
}

// Counterpart to create_matrix.
void destroy_matrix(Matrix *matrix) {
	if (!matrix) {
		return;
	}

	if (matrix->data) {
		for (size_t row = 0; row < matrix->rows; row++) {
			if (matrix->data[row]) {
				free(matrix->data[row]);
			}
		}

		free(matrix->data);
	}

	free(matrix);
}



int main(int argc, char *argv[]) {
	error_t error = EXIT_OK;

	Matrix *matrix = create_matrix(0, 0, &error);
}
