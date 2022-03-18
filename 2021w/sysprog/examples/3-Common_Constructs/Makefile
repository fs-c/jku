all:    simple-loops print strings if

clean:
	rm -f simple-loops print strings if
	rm -f *.o

simple-loops: simple-loops.s
	as -o simple-loops.o simple-loops.s --gstabs+
	ld -o simple-loops simple-loops.o

print: print.s
	as -o print.o print.s --gstabs+
	ld -o print print.o -lc -dynamic-linker /lib64/ld-linux-x86-64.so.2

strings: strings.s
	as -o strings.o strings.s --gstabs+
	ld -o strings strings.o -lc -dynamic-linker /lib64/ld-linux-x86-64.so.2

if: if.s
	as -o if.o if.s --gstabs+
	ld -o if if.o

