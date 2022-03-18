all: exit maximum memory

clean:
	rm -f exit maximum memory
	rm -f *.o

exit: exit.s
	as -o exit.o exit.s --gstabs+
	ld -o exit exit.o

memory: memory.s
	as -o memory.o memory.s --gstabs+
	ld -o memory memory.o

maximum: maximum.s
	as -o maximum.o maximum.s --gstabs+
	ld -o maximum maximum.o
