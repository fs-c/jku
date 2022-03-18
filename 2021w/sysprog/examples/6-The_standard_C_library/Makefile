CC=gcc
CFLAGS=-Wall -g

SOURCES=$(wildcard *.c)
EXECUTABLES=$(SOURCES:%.c=%)

all: $(EXECUTABLES)
	rm -rf *.dSYM
	
clean:
	rm -rf $(EXECUTABLES) *.dSYM