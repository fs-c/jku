#ifndef GAME_2048_H_INCLUDED
#define GAME_2048_H_INCLUDED

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

// struct for the coordinates on the board
//      x ... coordinate in hoizontal direction
//      y ... coordinate in vertical direction
typedef struct Position {
  unsigned char x;
  unsigned char y;
} Position;

// struct for element on the board
//      pos   ... position in x/y coordinates
//      value ... value of the cell
typedef struct Cell {
  Position pos;
  unsigned int value;
} Cell;

// struct for the game board
//      size  ... size the array in both directions (NxN; N=size)
//      cells ... pointer to 2d-array of pointers to Cells
typedef struct Board {
  unsigned int size;
  Cell ***cells;
} Board;

// Error codes used as return value for this program and internaly to check if 
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
  STATE_ONGOING,          // no interrup of the game, default state
  STATE_FINISH,           // finish state reached if the value 2048 is reached
  STATE_NO_MORE_MOVES     // if there are no more moves possible (e.g. no empty space to move the board values, no two cells with same values neighboring each other
} BoardState;


/*  create_board  */
/*
  function to create a new board to play on, incl. memory allocation
  
  * Parameters:
    const unsigned int size : size of the board (NxN), used for width and height
    const unsigned int seed : seed value used for srand to initialize the random number generation
    Error_code *err         : Typedef of enum used to check for invalid behavior. (call-by-ref)
  
  * Return value:
    Board *board            : pointer to struct Board, which contains the array of Cells and the size of the sides
*/
Board *create_board(const unsigned int size, const unsigned int seed, ErrorCode *err);


/*  remove_board  */
/*
  remove board, which is passed via parameters and free memory

  * Parameters:
    Board *board            : pointer to struct Board, which contains the array of Cells and the size of the sides
*/
ErrorCode destroy_board(Board *board);


/*  move_direction  */
/*
  move the board values to the given direction
  
  * Parameters:
    Board *board       : pointer to struct Board, which contains the array of Cells and the size of the sides
    Directions dir     : enum, that descripes the direction of the move (up, down, left, right); in this case the direction to move
    Error_code *err    : Typedef of enum used to check for invalid behavior. (call-by-ref)
	
  * Return value:
    Board_state        : enum, that describes the current state of the board
*/
BoardState move_direction(Board *board, Direction dir, ErrorCode *err);


/*  check_board_state  */
/*
  check the state of the board: if finish condition reached, if empty cells available or if moves possible

  * Parameters:
    Board *board       : pointer to struct Board, which contains the array of Cells and the size of the sides

  * Return value:
    Board_state        : enum, that describes the current state of the board
*/
BoardState check_board_state(Board *board);


/*  print_board  */
/*
  print the current board state to the terminal

  * Parameters:
    Board *board    : pointer to struct Board, which contains the array of Cells and the size of the sides
    bool with_clear : if set to 0, no clear is done for the terminal, else the terminal is cleared and overwritten
*/
ErrorCode print_board(Board *board, bool with_clear);

#endif // GAME_2048_H_INCLUDED
