CC=gcc
CFLAGS=-DDEBUG -Wall -Wextra -g

all: game_2048

game_2048: main.o game_2048.o
	${CC} main.o game_2048.o -o game_2048

game2048.o: game_2048.c game_2048.h

main.o: main.c game_2048.h


clean:
	rm -f *.o game_2048

.PHONY: all clean

