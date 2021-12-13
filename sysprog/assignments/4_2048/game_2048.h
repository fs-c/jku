#pragma once

#include <stddef.h>

// Note that I have changed some of the given structs to use an appropiately
// redefined type size_t.

// If DEBUG is defined, define a debug() macro function that works like printf() 
// but also appends a debug tag and the name of the calling function. Depends on 
// stdio being included.
#ifdef DEBUG

	#define debug(...)\
		printf("[debug] [%s] ", __FUNCTION__ );\
		printf(__VA_ARGS__);\
		putchar('\n');\

#else

	#define debug(...)\
		;\

#endif

// Terminal control codes
#define COLOR_RED           "\x1b[31m"
#define COLOR_GREEN         "\x1b[32m"
#define COLOR_YELLOW        "\x1b[33m"
#define COLOR_BLUE          "\x1b[34m"
#define COLOR_MAGENTA       "\x1b[35m"
#define COLOR_CYAN          "\x1b[36m"
#define COLOR_BR_RED        "\x1b[91m"
#define COLOR_BR_GREEN      "\x1b[92m"
#define COLOR_BR_YELLOW     "\x1b[93m"
#define COLOR_BR_BLUE       "\x1b[94m"
#define COLOR_BR_MAGENTA    "\x1b[95m"
#define COLOR_BR_CYAN       "\x1b[96m"
#define COLOR_RESET         "\x1b[0m"

#define CLEAR_SCREEN        "\x1b[2J"

// Define an internal size_t (thus isize_t) for use with custom structs. 
typedef unsigned int isize_t;

// Struct for program arguments.
//	seed	... seed for the PRNG
//	in	... stream to read input from
//	out	... stream to write output to
typedef struct Arguments {
	unsigned int seed;
	FILE *in;
	FILE *out;
} Arguments;

// Struct for the coordinates on the board.
//      x ... coordinate in horizontal direction
//      y ... coordinate in vertical direction
typedef struct Position {
	// Why does this have to be unsigned char? The largest possible position
	// for the given board struct is (UINT_MAX, UINT_MAX) and UINT_MAX > UINT_CHAR
	// by definition. (Assuming isize_t = unsigned int.)
	unsigned char x;
	unsigned char y;
} Position;

// Struct for element on the board.
//      pos   ... position in x/y coordinates
//      value ... value of the cell
typedef struct Cell {
	Position pos;
	unsigned int value;
} Cell;

// Struct for the game board.
//      size  ... size the array in both directions (NxN; N=size)
//      cells ... pointer to 2d-array of pointers to Cells
typedef struct Board {
	isize_t size;
	Cell ***cells;
} Board;

// Error codes used as return value for this program and internally to check if 
// early abort needed
typedef enum {
	EXIT_OK         = 0,
	EXIT_ARGS       = 1,  // invalid program arguments
	EXIT_IO         = 2,  // stream reading/writing
	EXIT_OUT_OF_MEM = 3,  // malloc failure
	EXIT_INTERNAL   = 4,  // anything else
} ErrorCode;

// Possible directions to deal with; used for input detection and application 
// on the board
typedef enum {
	DIR_UP,         // input/procedure for up direction
	DIR_DOWN,       // input/procedure for down direction
	DIR_LEFT,       // input/procedure for left direction
	DIR_RIGHT,      // input/procedure for right direction
	DIR_UNDEFINED   // any other input
} Direction;

// current board state; used for checks and output
typedef enum {
	STATE_ONGOING,          // no interruption of the game, default state
	STATE_FINISH,           // finish state reached if the value 2048 is
				// reached
	STATE_NO_MORE_MOVES     // if there are no more moves possible (e.g. no 
				// empty space to move the board values, no two
				// cells with same values neighboring each other)
} BoardState;

// Create a new board of the given size (interpreted as size x size cells) and 
// initialize it with two random values.
Board *create_board(const isize_t size, ErrorCode *err);

// Free the given board which was previously created with `create_board`.
ErrorCode free_board(Board *board);

// Apply a direction/move command to the given board.
BoardState move_direction(Board *board, Direction dir);

// Add 2 or 4 (chosen randomly) to a random position on the given board, 
// following the required "order of randomness". Returns EXIT_OK even if the 
// board is full (i. e. if no new value was added).
ErrorCode add_number(Board *board);
