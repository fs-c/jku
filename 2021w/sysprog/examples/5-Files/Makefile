all: toupper

clean:
	rm -f toupper
	rm -f *.o

toupper: toupper.s
	as -o toupper.o toupper.s --gstabs+
	ld -o toupper toupper.o