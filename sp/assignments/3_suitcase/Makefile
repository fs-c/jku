all: suitcase

CC = gcc
CFLAGS = -g -std=c17 -Wall

cleansuitcase:
	rm -f suitcase
	rm *.o

clean: cleansuitcase

game-io.o: game-io.c game-io.h
	$(CC) $(CFLAGS) -c game-io.c

suitcase.o: suitcase.c
	$(CC) $(CFLAGS) -c suitcase.c

suitcase: game-io.o suitcase.o
	$(CC) $(CFLAGS) -o suitcase suitcase.o game-io.o

all: suitcase

clean:
	rm -f suitcase

