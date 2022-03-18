#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "game_2048.h"

#define BOARD_SIZE 4

// Process the given arguments, optionally opening streams if required. The 
// callee will have to close any streams that were opened. If the input or output
// pointer is NULL, something went wrong. Modifies argv.
Arguments process_arguments(int argc, char *argv[], ErrorCode *err) {
	*err = EXIT_OK;

	// Set up args struct with defaults
	Arguments args = { 1, stdin, stdout };

	for (int i = 1; i < argc; i++) {
		char *key = strtok(argv[i], "=");
		char *value = strtok(NULL, "=");

		if (!key || !value) {
			debug("ignoring invalid argument '%s' (%d)", argv[i], i);
		}

		if (!strcmp(key, "seed")) {
			args.seed = (unsigned int)strtoul(value, NULL, 10);

			debug("seed is %d", args.seed);
		} else if (!strcmp(key, "in")) {
			args.in = fopen(value, "r");

			debug("input argument is %s", value);
		} else if (!strcmp(key, "out")) {
			args.out = fopen(value, "w");

			debug("output argument is %s", value);
		} else {
			debug("ignoring invalid argument key '%s' (%d)", key, i);
		}
	}

	if (!args.in || !args.out) {
		debug("failed opening %s stream(s)",
			!args.in ? !args.out ? "both" : "input" : "output");

		// Either the file didn't exist (invalid argument) or something
		// went wrong while opening the file (i/o error).
		*err = errno == ENOENT ? EXIT_ARGS : EXIT_IO;
	}

	return args;
}

// Read a single movement instruction (direction) from the given stream.
Direction read_direction(FILE *stream) {
	if (stream == stdin) {
		puts("Enter w, a, s, d for direction:");
	}

	char c;

	// Read the current char, skipping newlines.
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

// Move the cursor to a given position on the terminal.
void move_cursor(int x, int y) {
	printf("\x1b[%d;%dH", y, x);
}

// Get a color control code for a given cell value. Guaranteed
// to be stable but will repeat for values >2^11.
char *get_color(unsigned int value) {
	static char colors[11][6] = {
		COLOR_RED, COLOR_GREEN, COLOR_BLUE, COLOR_MAGENTA, 
		COLOR_CYAN, COLOR_BR_RED, COLOR_BR_GREEN, COLOR_BR_YELLOW,
		COLOR_BR_BLUE, COLOR_BR_MAGENTA, COLOR_BR_CYAN
	};

	size_t index = 0;

	while (value /= 2) {
		index++;
	}

	return colors[(index - 1) % 11];
}

// Write the given board and round number to the given stream. Produces human-readable 
// and colored output when stream is stdout and the given standard format otherwise.
// If with_clear is true, attempts to clear the console (ignored if stream != stdout).
ErrorCode print_state(FILE *stream, Board *board, unsigned int round, bool with_clear) {
	if (!board || !stream) {
		return EXIT_INTERNAL;
	}

	// Whether or not to format the output nicely 
	const bool nice = stream == stdout;

	if (with_clear && nice) {
		move_cursor(0, 0);
		puts(CLEAR_SCREEN);
	}


	fprintf(stream, "%s%d%s", nice ? "Round: " : "round:", round,
		nice ? "\n\n" : "\n");

	for (isize_t i = 0; i < board->size; i++) {
		for (isize_t j = 0; j < board->size; j++) {
			unsigned int value = board->cells[i][j]->value;

			if (nice) {
				fprintf(stream, "%s%4d%s", get_color(value), value, COLOR_RESET);
			} else {
				fprintf(stream, "%d", board->cells[i][j]->value);
			}

			putc(nice ? ' ' : ',', stream);
		}

		putc('\n', stream);
	}


	return EXIT_OK;
}

int main(int argc, char *argv[]) {
	ErrorCode err = EXIT_OK;

	Arguments args = process_arguments(argc, argv, &err);

	if (err != EXIT_OK) {
		fprintf(stderr, "Error processing arguments: %d\n", err);

		return err;
	}

	srand(args.seed);

	Board *board = create_board(BOARD_SIZE, &err);

	if (err != EXIT_OK || !board) {
		fprintf(stderr, "Error creating board: %d\n", err);

		return err;
	}

	unsigned int round = 0;

	print_state(args.out, board, round, true);

	bool moved;
	Direction dir;

	// Main game loop, kepe reading movement commands
	while ((dir = read_direction(args.in)) != DIR_UNDEFINED) {
		round++;
		moved = false;

		// Execute the move
		BoardState state;
		if ((state = move_direction(board, dir, &moved)) != STATE_ONGOING) {
			// If no more moves were possible, exit
			break;
		}

		// If we actually moved something, add a new number
		if (moved) {
			add_number(board);
		}

		print_state(args.out, board, round, true);
	}

	free_board(board);

	// Might be set to stdin/out but closing those won't hurt at this point
	fclose(args.in);
	fclose(args.out);

	return err;
}
