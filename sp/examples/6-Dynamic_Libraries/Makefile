all: helloworld-lib factorial-main

clean:
	rm -f helloworld-lib factorial-lib factorial-main
	rm -f *.o
	rm -f *.so

helloworld-lib: helloworld-lib.s
	as -o helloworld-lib.o helloworld-lib.s -gstabs++
	ld -o helloworld-lib -dynamic-linker /lib64/ld-linux-x86-64.so.2 -lc helloworld-lib.o

libfactorial.so: factorial-lib.s
	as -o factorial-lib.o factorial-lib.s -gstabs++
	ld -o libfactorial.so -shared factorial-lib.o

factorial-main: libfactorial.so factorial-main.s
	as -o factorial-main.o factorial-main.s -gstabs++
	ld -o factorial-main -L . -dynamic-linker /lib64/ld-linux-x86-64.so.2 -lfactorial factorial-main.o
