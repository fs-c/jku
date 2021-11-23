#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <errno.h>
#include <unistd.h>
#include <limits.h>
#include <string.h>

#include "game-io.h"

static char input_buffer[81];

static bool isInteractive(int fileno);
static char* readInputLine();

yes_no_retry_t askPlayerYesNo()
{
    char* input_line = readInputLine();
    if (!strcmp(input_line, "y\n")) {
        return Yes;
    }
    else if (!strcmp(input_line, "n\n")) {
        return No;
    }
    else {
        return Retry;
    }
}

bool askPlayerForNumber(unsigned int* number)
{
    char* input_line = readInputLine();
    char* parse_end_ptr = NULL;
    long long_num = strtol(input_line, &parse_end_ptr, 10);
    if ((errno != 0) || (parse_end_ptr == input_line) || (long_num >= USHRT_MAX) || (number <= 0)) {
        errno = 0;
        return false;
    }
    *number = long_num;
    return true;
}

static char* readInputLine()
{
    assert(errno == 0);
    char* input_line = fgets(input_buffer, sizeof(input_buffer), stdin);
    assert(errno == 0);
    if (input_line == NULL) {
        printf("End of input reached.\n");
        exit(EXIT_FAILURE);
    };
    if (!isInteractive(STDIN_FILENO)) {
        // print inputs on non-interactive input stream so that
        // user selections are visisble in the output
        // like they would be in an interactive session
        printf("%s", input_line);
    }
    return input_line;
}

static bool isInteractive(int fileno)
{
    assert(errno == 0);
    if (isatty(fileno)) {
        return true;
    }
    else {
        // isatty will have set errno, so we have to clear it
        assert(errno == ENOTTY);
        errno = 0;
        return false;
    }
}
