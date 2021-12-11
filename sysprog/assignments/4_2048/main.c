#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "game_2048.h"

#define BOARD_SIZE 4

// Processes the given arguments, optionally opening streams if required. The 
// callee will have to close any streams that were opened. If the input or output
// pointer is NULL, something went wrong. Modifies argv.
Arguments process_arguments(int argc, char *argv[], ErrorCode *err) {
	*err = EXIT_OK;

	// Set up args struct with defaults.
	Arguments args = { 1, stdin, stdout };

	for (int i = 1; i < argc; i++) {
		char *key = strtok(argv[i], "=");
		char *value = strtok(NULL, "=");

		if (!key || !value) {
			debug("ignoring invalid argument '%s' (%d)", argv[i], i);
		}

		if (!strcmp(key, "seed")) {
			args.seed = (unsigned int)strtoul(value, NULL, 10);
			
			// TODO: Maybe do some error checking here? Probably not
			// particularly useful since strtoul just returns 0 on err.

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

// Write the given board and round number to the given stream. Produces uman-readable 
// and colored output when stream is stdout and the given standard format otherwise.
// If with_clear is true, attempts to clear the console (ignored if stream != stdout).
ErrorCode print_state(FILE *stream, Board *board, unsigned int round, bool with_clear) {
	if (!board || !stream) {
		return EXIT_INTERNAL;
	}

	// Whether or not to format the output nicely 
	const bool nice = stream == stdout;

	if (with_clear && nice) {
		// TODO: system("clear") is a horrible solution (not portable, 
		// user might lose data because of it, etc.), find a better way.
	}


	fprintf(stream, "%s%d%s", nice ? "Round: " : "round:", round,
		nice ? "\n\n" : "\n");

	for (isize_t i = 0; i < board->size; i++) {
		for (isize_t j = 0; j < board->size; j++) {
			if (nice) {
				fprintf(stream, "%4d", board->cells[i][j]->value);
			} else {
				fprintf(stream, "%d", board->cells[i][j]->value);
			}

			putc(nice ? ' ' : ',', stream);
		}

		putc('\n', stream);
	}

	return EXIT_OK;
}

// A `save_current_state(Board *, FILE *, round)` was outlined here but I didn't
// see a necessity for it yet.

int main(int argc, char *argv[]) {
	ErrorCode err = EXIT_OK;

	Arguments args = process_arguments(argc, argv, &err);

	if (err != EXIT_OK) {
		fprintf(stderr, "Error processing arguments: %d\n", err);

		return err;
	}

	// Set up PRNG
	srand(args.seed);

	// Set up board
	Board *board = create_board(BOARD_SIZE, &err);

	if (err != EXIT_OK || !board) {
		fprintf(stderr, "Error creating board: %d\n", err);

		return err;
	}

	unsigned int round = 0;

	print_state(args.out, board, round, true);

	Direction dir;
	while ((dir = read_direction(args.in)) != DIR_UNDEFINED) {
		round++;

		move_direction(board, dir);
		add_number(board);

		print_state(args.out, board, round, true);
	}

	free_board(board);

	// These might be set to stdin/out but we don't care.
	fclose(args.in);
	fclose(args.out);

	return err;
}
