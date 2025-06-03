obj-m += loader.o

all: loader code.o load.info

loader: loader.c
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

code.o: code.c
	gcc -c code.c -fPIC -o code.o

load.info: code.o extract_load_info.sh
	./extract_load_info.sh code.o > load.info

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean

run:
	/sbin/insmod ./loader.ko
	/sbin/rmmod ./loader.ko
