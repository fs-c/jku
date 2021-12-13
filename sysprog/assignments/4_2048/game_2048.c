#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "game_2048.h"

#define WIN_CONDITION 2048

// The following is implemented such that the indices of cells in board.cells 
// always correspond to their x and y values. This makes it easier to think about 
// but it also makes said values redundant. Cells are never moved around, but their 
// actual values are. I hope that's not going against the spirit of the assignment.

// Check if the given board has free cells.
bool has_free_cells(Board *board) {
	bool has_free = false;

	for (isize_t i = 0; i < board->size * board->size; i++) {
		if ((*(*board->cells + i))->value == 0) {
			has_free = true;
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

// isize_t _move_cell(Cell **cell, isize_t delta, isize_t direction, isize_t steps) {
// 	// Ignore empty cells
// 	if ((*cell)->value == 0) {
// 		return 0;
// 	}

// 	// Keep track of whether or not we already merged the current cell
// 	bool has_merged = false;

// 	// Keep track of the step where we merged a value, this will be the 
// 	// return value
// 	isize_t last_merge = 0;

// 	for (isize_t i = 0; i < steps; i++) {
// 		isize_t offset = i * delta * direction;

// 		Cell *cur = *(cell + offset);
// 		Cell *next = *(cell + offset + delta);

// 		if (next->value == 0) {
// 			next->value = cur->value;
// 			cur->value = 0;
// 		} else if (next->value == cur->value && !has_merged) {
// 			next->value *= 2;
// 			cur->value = 0;

// 			has_merged = true;
// 			last_merge = i;
// 		}
// 	}

// 	return last_merge;
// }

isize_t _move_direction(Board *board, Direction dir, bool dry_run, BoardState *state) {
	// Keep track of moves, this will be the return value
	isize_t moves = 0;

	const bool reverse = dir == DIR_DOWN || dir == DIR_RIGHT;
	const bool horizontal = dir == DIR_LEFT || dir == DIR_RIGHT;

	debug("moving board %lx (reverse: %d, horizontal: %d)", (uintptr_t)board,
		reverse, horizontal);

	// For every row (left/right) or column (up/down)...
	for (isize_t outer = 0; outer < board->size; outer++) {
		// Keep track of where we last moved a value to
		isize_t cursor = reverse ? board->size - 1 : 0;

	 	// Start from the direction we're moving to, skip the first cell
	 	isize_t i = reverse ? board->size - 1 : 1;
	 	for (; reverse ? i > 0 : i <= board->size; reverse ? i-- : i++) {			
	 		Cell *cell = horizontal ? board->cells[outer][i - 1]
	 			: board->cells[i - 1][outer];

	 		// We only care about cells with values in them
	 		if (cell->value == 0) {
	 			continue;
	 		}

	 		// Movement direction starting from `i`
	 		const isize_t offset = reverse ? 1 : -1;

	 		// A given cell may only merge once per "move"
	 		bool has_merged = false;
			// To make sure 8 4 4 0 -> 8 8 0 0 and not 16 0 0 0.

	 		// Make cell "bubble" to its new place by iterating
	 		// backwards relative to the direction of the outer loop.
			// Stop _before_ the last place we moved a value _from_
			// to make sure 4 4 8 0 -> 8 8 0 0 and not 16 0 0 0.
	 		isize_t j = i - 1;
	 		for (; reverse ? j < cursor : j > cursor; j += offset) {
	 			Cell *cur = horizontal ? board->cells[outer][j]
	 				: board->cells[j][outer];

	 			Cell *next = horizontal ? board->cells[outer][j + offset]
	 				: board->cells[j + offset][outer];

	 			if (next->value == 0) {
					moves++;

					if (!dry_run) {
		 				next->value = cur->value;
		 				cur->value = 0;
					}
	 			} else if (next->value == cur->value && !has_merged) {
					moves++;

					if (!dry_run) {
		 				next->value *= 2;
		 				cur->value = 0;
					}

					if (next->value == WIN_CONDITION) {
						*state = STATE_FINISH;
					}

					has_merged = true;
					cursor = j;
				}
			}
		}
	}

	return moves;
}

Cell **__move_cell(Cell **start, Cell **end, ptrdiff_t delta) {
	debug("delta: %ld", delta);

	bool has_merged = false;
	Cell **last_merge = end;

	// Make sure we don't end up in an infinite loop
	// if (((uintptr_t)start / (uintptr_t)end) % delta) {
	// 	debug("end pointer unreachable with delta %ld", delta);

	// 	return NULL;
	// }

	while (start != end) {
		Cell *cur = *(start);
		Cell *next = *(start + delta);

		start += delta;

		if (!cur->value) {
			continue;
		}

		if (next->value == 0) {
			next->value = cur->value;
			cur->value = 0;
		} else if (cur->value == next->value && !has_merged) {
			next->value *= 2;
			cur->value = 0;

			has_merged = true;
			// Make sure to subtract delta because we already added
			// it for the next iteration at this point
			last_merge = start - delta;
		}
	}

	return last_merge;
}

void __move_direction(Board *board, Direction dir) {
	const bool reverse = dir == DIR_DOWN || dir == DIR_RIGHT;
	const bool horizontal = dir == DIR_LEFT || dir == DIR_RIGHT;

	const ptrdiff_t direction = reverse ? -1 : 1;

	// How far it is from one cell to its neighbour in the given context
	const ptrdiff_t delta = horizontal
		? direction
		: (ptrdiff_t)board->size * direction;

	debug("reverse: %d, horizontal: %d, direction: %ld, delta: %ld (%d)",
		reverse, horizontal, direction, delta, dir);

	for (isize_t outer = 0; outer < board->size; outer++) {
		Cell **cursor = NULL;

		debug("open context");

		for (isize_t inner = 1; inner < board->size; inner++) {
			const isize_t index = reverse
				? (board->size - 1) - inner
				: inner;

			const isize_t offset = horizontal
				? (outer * board->size) + index
				: (index * board->size) + outer;

			debug("outer: %d, inner: %d, index: %d, offset: %d",
				outer, inner, index, offset);

			Cell **begin = *board->cells + offset;
			Cell **end = cursor ? cursor
				: begin + (inner * delta * -1);

			cursor = __move_cell(begin, end, delta * -1);

			
			// Cell **cur = *board->cells + offset;
			// debug("noseg");

			// if ((*cur)->value == 0) {
			// 	continue;
			// }

			// for (isize_t j = cursor; j < inner; j++) {
			// 	debug("j: %d, d: %ld", j, delta * j);

			// 	Cell *next = *(cur - (delta * j));

			// 	if (next->value == 0) {
			// 		next->value = (*cur)->value;
			// 		(*cur)->value = 0;
			// 	} else if (next->value == (*cur)->value) {
			// 		next->value *= 2;
			// 		(*cur)->value = 0;

			// 		cursor = j;
			// 	}
			// }
		}

		debug("close context");
	}
}

BoardState cell_has_moves(Cell **cell, isize_t offset) {
	Cell *cur = *cell;

	Cell *next = *cell + offset;

	if (cur->value == next->value) {
		return STATE_ONGOING;
	}

	return STATE_NO_MORE_MOVES;
}

bool possible_moves(Board *board) {
	for (isize_t i = board->size + 1; i < (board->size * board->size) - board->size - 1; i++) {
		Cell **cell = *board->cells + 1;
		
		if (
			cell_has_moves(cell, 1) == STATE_ONGOING || 
			cell_has_moves(cell, -1) == STATE_ONGOING ||
			cell_has_moves(cell, board->size) == STATE_ONGOING ||
			cell_has_moves(cell, board->size * -1) == STATE_ONGOING
		) {
			return true;
		}
	}

	return false;
}


BoardState move_direction(Board *board, Direction dir) {
	BoardState state = STATE_ONGOING;

	// if (!possible_moves(board)) {
	// 	return STATE_NO_MORE_MOVES;
	// }

	_move_direction(board, dir, false, &state);

	return state;
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

	// x = rand() % 2 is either 1 or 2 so (x + 1) * 2 is either 2 or 4
	unsigned int value = ((rand() % 2) + 1) * 2;

	// We know that a free cell exists, so just keep trying to add a value
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

	// Dead code path unless something is going horribly wrong
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
