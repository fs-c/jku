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

Board *allocate_board(const isize_t size, ErrorCode *err) {
	Board *board = malloc(sizeof(Board));

	if (!board) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	board->size = size;

	// Allocate a continuous block of memory where cell pointers are stored
	Cell **cell_ptrs = malloc(board->size * board->size * sizeof(Cell *));

	if (!cell_ptrs) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	// Allocate space for "columns", these will just be pointers into that 
	// continuous block
	board->cells = malloc(board->size * sizeof(Cell **));

	if (!board->cells) {
		*err = EXIT_OUT_OF_MEM;

		return NULL;
	}

	// Populate "columns" and cells
	for (isize_t i = 0; i < board->size; i++) {
		board->cells[i] = cell_ptrs + (i * board->size);

		for (isize_t j = 0; j < board->size; j++) {
			// Make sure cells have their fields default to zero
			board->cells[i][j] = calloc(1, sizeof(Cell));

			if (!board->cells[i][j]) {
				*err = EXIT_OUT_OF_MEM;

				return NULL;
			}
		}
	}

	// Because we allocated the cell pointers as a continuous block we can
	// refer to a cell by doing
	// 	(*(*board->cells + (y * board->size) + x))->value, OR
	//	board->cells[y][x]->value.
	// The latter means that the specification was followed properly while the
	// former will be useful in move_direction.

	debug("allocated board %lx", (uintptr_t)board);

	return board;
}


ErrorCode free_board(Board *board) {
	if (!board) {
		return EXIT_INTERNAL;
	}

	for (isize_t i = 0; i < board->size * board->size; i++) {
		free(*(*board->cells + i));
	}

	free(*board->cells);
	free(board->cells);
	free(board);

	return EXIT_OK;
}


BoardState move_direction(Board *board, Direction dir) {
	// return _move_direction(board, dir);

	const bool reverse = dir == DIR_DOWN || dir == DIR_RIGHT;
	const bool horizontal = dir == DIR_LEFT || dir == DIR_RIGHT;

	debug("moving board %lx (reverse: %d, horizontal: %d)", (uintptr_t)board,
		reverse, horizontal);

	// `fixed` represents the row for left/right and column for up/down
	for (isize_t fixed = 0; fixed < board->size; fixed++) {
		// Keep track of where we last moved a value to
		isize_t cursor = reverse ? board->size - 1 : 0;

	 	// Start from the direction we're moving to, skip the first cell
	 	isize_t i = reverse ? board->size - 1 : 1;
	 	for (; reverse ? i > 0 : i <= board->size; reverse ? i-- : i++) {			
	 		Cell *cell = horizontal ? board->cells[fixed][i - 1]
	 			: board->cells[i - 1][fixed];

	 		// We only care about cells with values in them
	 		if (cell->value == 0) {
	 			continue;
	 		}

	 		// Movement direction starting from `i`.
	 		const isize_t offset = reverse ? 1 : -1;

	 		// A given cell may only merge once per "move"
	 		bool has_merged = false;
			// To make sure 8 4 4 -> 8 8 0 0.

	 		// Make cell "bubble" to its new place by iterating
	 		// backwards relative to the direction of the outer loop.
			// Stop _before_ the last place we moved a value _from_
			// to make sure 4 4 8 0 -> 8 8 0 0.
	 		isize_t j = i - 1;
	 		for (; reverse ? j < cursor : j > cursor; j += offset) {
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
					cursor = j;
				}
			}
		}
	}

	return STATE_ONGOING;
}

// Add 2 or 4 (chosen randomly) to a random position on the given board, 
// following the required "order of randomness". Returns EXIT_OK even if the 
// board is full (i. e. if no new value was added).
ErrorCode add_number(Board *board) {
	debug("adding number to board %lx", (uintptr_t)board);

	if (!board) {
		return EXIT_INTERNAL;
	}

	if (!has_free_cells(board)) {
		return EXIT_OK;
	}

	// x = rand() % 2 is either 1 or 2, (x + 1) * 2 is either 2 or 4
	unsigned int value = ((rand() % 2) + 1) * 2;

	while (true) {
		isize_t x = rand() % board->size;
		isize_t y = rand() % board->size;

		if (board->cells[y][x]->value == 0) {
			board->cells[y][x]->value = value;
			board->cells[y][x]->pos = (Position){ x, y };

			debug("added %d to board %lx at %d, %d", value,
				(uintptr_t)board, x, y);

			return EXIT_OK;
		}
	}

	return EXIT_INTERNAL;
}

Board *create_board(const isize_t size, ErrorCode *err) {
	debug("creating board of size %d", size);

	if (size <= 0) {
		*err = EXIT_INTERNAL;

		return NULL;
	}

	Board *board = allocate_board(size, err);

	if (*err != EXIT_OK) {
		return NULL;
	}

	*err = add_number(board);
	*err = add_number(board);

	return board;
}
