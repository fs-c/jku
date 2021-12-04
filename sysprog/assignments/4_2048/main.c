#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "game_2048.h"

#define BOARD_SIZE 4

// Read a movement instruction (direction) from the given stream.
Direction read_direction(FILE *stream) {
	char c;

	puts("Enter w, a, s, d for direction:");

	while((c = getc(stream)) == '\n');

	if (c == EOF) {
		return DIR_UNDEFINED;
	}

	switch (c) {
		case 'w': return DIR_UP;
		case 'a': return DIR_LEFT;
		case 's': return DIR_DOWN;
		case 'd': return DIR_RIGHT;
	}

	return DIR_UNDEFINED;
}

// A `save_current_state(Board *, FILE *, round)` was outlined here but I didn't
// see a necessity for it.

int main(int, char **) {
	ErrorCode err = EXIT_OK;

	Board *board = create_board(BOARD_SIZE, 0, &err);

	if (err != EXIT_OK || !board) {
		printf("Error creating board: %d\n", err);

		return err;
	}

	print_board(board, true);

	Direction d;
	while ((d = read_direction(stdin)) != DIR_UNDEFINED) {
		move_direction(board, d, NULL);
		add_number(board, 0);

		print_board(board, true);
	}

	free_board(board);

	return err;
}
