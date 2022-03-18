all: alloc-demo

clean:
	rm -f alloc-demo
	rm -f *.o

alloc-demo: alloc.s alloc-demo.s
	as -o alloc.o alloc.s -gstabs++
	as -o alloc-demo.o alloc-demo.s -gstabs++
	ld -o alloc-demo alloc.o alloc-demo.o