CC=gcc
CFLAGS=-Wall -g -m32

SOURCES=$(wildcard *.c)
EXECUTABLES=$(SOURCES:%.c=%)

all: $(EXECUTABLES)
	
clean:
	rm -rf $(EXECUTABLES) 