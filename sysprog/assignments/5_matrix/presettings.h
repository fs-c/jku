#ifndef PRESETTINGS_H
#define PRESETTINGS_H

#define EXIT_OK 0
#define EXIT_ARGS 1
#define EXIT_IO 2
#define EXIT_INCOMPATIBLE_DIM 3
#define EXIT_NUMBER_TOO_BIG 4
#define EXIT_INVALID_MATRIX 5
#define EXIT_INVALID_NUMBER 6
#define EXIT_OUT_OF_MEM 7

// Maximum length of a matrix element
#define MAX_LENGTH 255
// Maximum length of a line, should be a reasonable default
#define MAX_LINE_LENGTH 1023

typedef unsigned char error_t;

static const char invalid_arg_num_str[]  = "Invalid number of arguments\n";

static const char in_out_error_str[]     = "Input/Output error\n";
static const char open_infile_err_str[]  = "Can't open input file '%s'\n";
static const char close_file_err_str[]   = "Couldn't close file\n";

static const char incompatible_dim_str[] = "Input matrices are not compatible for multiplication\n";

static const char out_of_mem_str[]       = "Out of memory\n";

static const char number_too_big_str[]   = "Input is too long (more than %d character)\n";

static const char invalid_number_str[]   = "Invalid number\n";
static const char leading_zero_str[]     = "Input contains leading zero numbers\n";

static const char invalid_matrix_str[]   = "Invalid matrix\n";

static const char unknown_error_str[]    = "Unknown error code %d\n";

#endif
