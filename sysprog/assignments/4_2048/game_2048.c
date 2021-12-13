#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "game_2048.h"

#define WIN_CONDITION 2048

// Implementation details:
// 	- The indices of cells in board.cells always correspond to their x and y
//	  values (i.e. board[y][x] <=> cell.y == y and cell.x == x). This makes 
//	  it easier to think about but it also makes said values redundant.
//	- Cell pointers are stored in a continuous block of memory, not 
//	  n = board->size separate blocks. See comment on allocate_board.

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

// Allocate a board of the given size, returns NULL and sets err on error. 
// Allocates *board->cells as a continuous block of memory which allows referring
// to a cell by doing
// 	(*(*board->cells + (y * board->size) + x))->value, OR
// 	board->cells[y][x]->value.
// The latter means that the specification was followed properly while the
// former will be useful when iterating through cells.
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

	debug("allocated board %lx", (uintptr_t)board);

	return board;
}

// Bubbles a value at *begin to (at most) *end, moving it over zeroes and merging 
// it with at most one equal value on the way. Determines the "next value" through
// (begin + delta). Returns the place where a value was last merged _from_. Performs
// no changes if dry_run is specified but outputs the expected return value.
Cell **bubble_cell(Cell **begin, Cell **end, ptrdiff_t delta, bool dry_run) {
	// TODO
	// Make sure we don't end up in an infinite loop
	// if (((uintptr_t)begin - (uintptr_t)end) % delta) {
	// 	debug("end pointer unreachable with delta %ld", delta);

	// 	return NULL;
	// }
	
	// Keep track of whether we already did a merge
	bool has_merged = false;
	// Keep track of where we last merged a cell from
	Cell **last_merge = end;

	while (begin != end) {
		Cell *cur = *(begin);
		Cell *next = *(begin + delta);

		begin += delta;

		if (!cur->value) {
			continue;
		}

		if (next->value == 0 && !dry_run) {
			next->value = cur->value;
			cur->value = 0;
		} else if (cur->value == next->value && !has_merged) {
			if (!dry_run) {
				next->value *= 2;
				cur->value = 0;
			}

			has_merged = true;
			last_merge = begin - delta;
		}
	}

	return last_merge;
}

bool has_available_moves(Board *board) {
	// For all rows but the last...
	for (isize_t x = 0; x < board->size - 1; x++) {
		// For all columns but the last...
		for (isize_t y = 0; y < board->size - 1; y++) {
		}
	}
}

// Public API begins here

// TODO: Handle possible board states
BoardState move_direction(Board *board, Direction dir) {
	const bool reverse = dir == DIR_DOWN || dir == DIR_RIGHT;
	const bool horizontal = dir == DIR_LEFT || dir == DIR_RIGHT;

	const ptrdiff_t direction = reverse ? -1 : 1;

	// How far it is from one cell to its neighbour in the given context
	const ptrdiff_t delta = horizontal
		? direction
		: (ptrdiff_t)board->size * direction;

	debug("board %lx: reverse %d (dir %ld), horizontal %d (offset %ld)",
		(uintptr_t)board, reverse, direction, horizontal, delta);
	
	// For every row (when left/right) or column (when up/down)...
	for (isize_t outer = 0; outer < board->size; outer++) {
		Cell **cursor = NULL;

		// For all cells in the row/column but the first one...
		for (isize_t inner = 1; inner < board->size; inner++) {
			// Pretend we're looping from the back if reverse is true
			const isize_t index = reverse
				? (board->size - 1) - inner
				: inner;

			// Address of the current cell relative to cell zero
			const isize_t offset = horizontal
				? (outer * board->size) + index
				: (index * board->size) + outer;

			Cell **begin = *board->cells + offset;
			// Never move beyond the cursor
			Cell **end = cursor ? cursor
				: begin + (inner * delta * -1);

			// Cursor is either equal to end or the place where we 
			// last merged a value from
			cursor = bubble_cell(begin, end, delta * -1, false);

			if ((*cursor - delta)->value == WIN_CONDITION) {
				return STATE_FINISH;
			}
		}
	}

	return STATE_ONGOING;
}

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
