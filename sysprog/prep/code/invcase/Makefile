all: invcase

clean:
	rm -f invcase
	rm -f *.o

invcase: invcase.s
	as -o invcase.o invcase.s --gstabs+
	ld -o invcase invcase.o