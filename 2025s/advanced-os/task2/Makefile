obj-m += kbd_buffer.o

all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean

load:
	/sbin/insmod ./kbd_buffer.ko

unload:
	/sbin/rmmod ./kbd_buffer.ko
