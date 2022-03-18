all: asm inline power

inline: inline.c
	gcc -Wall -ansi -pedantic -g -o inline inline.c

asm: inline.c
	gcc -Wall -ansi -pedantic -g inline.c -S -fverbose-asm

power2.o: power2.s
	as -o power2.o power2.s

power: power.c power2.o
	gcc -c -Wall -ansi -pedantic -g power.c -o power.o
	gcc -o power power.o power2.o

clean:
	rm -rf *.o *.dSYM inline inline.s power
