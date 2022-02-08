all: matrixmult

matrixmult: matrixmult.c presettings.h
	gcc -std=c17 -Wall -g -o matrixmult matrixmult.c presettings.h -fsanitize=address

clean:
	rm -f matrixmult testing
