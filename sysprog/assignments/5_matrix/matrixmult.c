#include "presettings.h"

#include <stdlib.h>

typedef struct Matrix {
	size_t rows;
	size_t columns;

	int **data;
} Matrix;

Matrix *create_matrix(size_t rows, size_t columns) {
	Matrix *matrix = malloc(sizeof(Matrix));

	matrix->rows = rows;
	matrix->columns = columns;

	matrix->data = malloc(rows * sizeof(int *));

	for (size_t row = 0; row < rows; row++) {
		matrix->data[row] = malloc(columns * sizeof(int));
	}

	return matrix;
}

error_t destroy_matrix() {

}

int main(int argc, char *argv[]) {

}
