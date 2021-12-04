#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "game_2048.h"

// The following is implemented such that the indices of cells in board.cells 
// always correspond to their x and y values. This makes it easier to think about 
// but it also makes said values redundant. Cells are never moved around, but their 
// actual values are. I hope that's not going against the spirit of the assignment.

// Check if the given board has free cells.
bool has_free_cells(Board *board) {
	bool has_free = false;

	for (unsigned int i = 0; i < board->size && !has_free; i++) {
		for (unsigned int j = 0; j < board->size && !has_free; j++) {			
			if (board->cells[i][j]->value == 0) {
				has_free = true;
			}
		}
	}

	return has_free;
}

bool has_possible_moves(Board *board) {

}

// Allocate a board of the given size (interpreted as size x size cells).
Board *allocate_board(const unsigned int size, ErrorCode *err) {
	Board *board = malloc(sizeof(Board));

	if (!board) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	board->size = size;

	// Allocate columns
	board->cells = malloc(size * sizeof(Cell *));

	if (!board->cells) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	// Allocate rows
	for (unsigned int i = 0; i < size; i++) {
		board->cells[i] = malloc(size * sizeof(Cell *));

		if (!board->cells[i]) {
			*err = EXIT_OUT_OF_MEM;

			return NULL;
		}

		// Allocate cells
		for (unsigned int j = 0; j < size; j++) {
			// Make sure cells have their fields default to zero
			board->cells[i][j] = calloc(1, sizeof(Cell));

			if (!board->cells[i][j]) {
				*err = EXIT_OUT_OF_MEM;

				return NULL;
			}
		}
	}

	debug("allocated board %lx", (uintptr_t)board);

	return board;
}

BoardState move_direction(Board *board, Direction dir) {
	const bool reverse = dir == DIR_DOWN || dir == DIR_RIGHT;
	const bool horizontal = dir == DIR_LEFT || dir == DIR_RIGHT;

	debug("moving board %lx (reverse: %d, horizontal: %d)", (uintptr_t)board,
		reverse, horizontal);

	// `fixed` represents the row for left/right and column for up/down
	for (unsigned int fixed = 0; fixed < board->size; fixed++) {
		// Start from the direction we're moving to
		unsigned int i = reverse ? board->size - 1 : 1;
		for (; reverse ? i > 0 : i <= board->size; reverse ? i-- : i++) {			
			Cell *cell = horizontal ? board->cells[fixed][i - 1]
				: board->cells[i - 1][fixed];

			// We only care about cells with values in them
			if (cell->value == 0) {
				continue;
			}

			// Movement direction starting from `i`.
			const unsigned int offset = reverse ? 1 : -1;

			// A given cell may only merge once per "move"
			bool has_merged = false;

			// Make cell "bubble" to its new place by iterating
			// backwards (relative to the direction of the outer loop).
			unsigned int j = i - 1;
			for (; reverse ? j < board->size - 1 : j > 0; j += offset) {
				Cell *cur = horizontal ? board->cells[fixed][j]
					: board->cells[j][fixed];

				Cell *next = horizontal ? board->cells[fixed][j + offset]
					: board->cells[j + offset][fixed];

				if (next->value == 0) {
					next->value = cur->value;
					cur->value = 0;
				} else if (next->value == cur->value && !has_merged) {
					next->value *= 2;
					cur->value = 0;

					has_merged = true;
				}
			}
		}
	}

	return STATE_ONGOING;
}

// Add 2 or 4 (chosen randomly) to a random position on the given board, 
// following the required "order of randomness". Returns EXIT_OK even if the 
// board is full (i. e. if no new value was added).
ErrorCode add_number(Board *board, const unsigned int seed) {
	debug("adding number to board %lx", (uintptr_t)board);

	if (!board) {
		return EXIT_INTERNAL;
	}

	if (!has_free_cells(board)) {
		return EXIT_OK;
	}

	srand(seed);

	// x = rand() % 2 is either 1 or 2, (x + 1) * 2 is either 2 or 4
	unsigned int value = ((rand() % 2) + 1) * 2;

	while (true) {
		unsigned int x = rand() % board->size;
		unsigned int y = rand() % board->size;

		if (board->cells[x][y]->value == 0) {
			board->cells[x][y]->value = value;
			board->cells[x][y]->pos = (Position){ x, y };

			debug("added %d to board %lx at %d, %d", value,
				(uintptr_t)board, x, y);

			return EXIT_OK;
		}
	}

	return EXIT_INTERNAL;
}

Board *create_board(
	const unsigned int size, const unsigned int seed, ErrorCode *err
) {
	debug("creating board of size %d with seed %d", size, seed);

	if (size <= 0) {
		*err = EXIT_INTERNAL;

		return NULL;
	}

	Board *board = allocate_board(size, err);

	if (*err != EXIT_OK) {
		return NULL;
	}

	*err = add_number(board, seed);
	*err = add_number(board, seed);

	return board;
}

ErrorCode free_board(Board *board) {
	if (!board) {
		return EXIT_INTERNAL;
	}

	for (unsigned int i = 0; i < board->size; i++) {
		for (unsigned int j = 0; j < board->size; j++) {
			if (!board->cells[i][j]) {
				return EXIT_INTERNAL;
			}

			free(board->cells[i][j]);
		}

		if (!board->cells[i]) {
			return EXIT_INTERNAL;
		}

		free(board->cells[i]);
	}

	free(board->cells);
	free(board);

	debug("freed board %lx", (uintptr_t)board);

	return EXIT_OK;
}

ErrorCode print_board(Board *board, bool with_clear) {
	if (!board) {
		return EXIT_INTERNAL;
	}

	if (with_clear) {
		printf(CLEAR_SCREEN);
	}

	for (unsigned int i = 0; i < board->size; i++) {
		for (unsigned int j = 0; j < board->size; j++) {
			printf("%4d ", board->cells[i][j]->value);
		}

		putchar('\n');
	}

	return EXIT_OK;
}
