all: function function-red power1 power2 binom factorial

clean:
	rm -f function function-red power1 power2 binom factorial
	rm -f *.o

function: function.s
	as -o function.o function.s --gstabs+
	ld -o function function.o

function-red: function-red.s
	as -o function-red.o function-red.s --gstabs+
	ld -o function-red function-red.o

power1: power1.s
	as -o power1.o power1.s --gstabs+
	ld -o power1 power1.o

power2: power2.s
	as -o power2.o power2.s --gstabs+
	ld -o power2 power2.o

binom: binom.s
	as -o binom.o binom.s --gstabs+
	ld -o binom binom.o

factorial: factorial.s
	as -o factorial.o factorial.s --gstabs+
	ld -o factorial factorial.o

