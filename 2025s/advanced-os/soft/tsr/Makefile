CFLAGS = -Werror -Wall -Wextra -Wpedantic -Wformat=2 -Wformat-overflow=2 -Wformat-truncation=2 -Wformat-security -Wnull-dereference -Wstack-protector -Wtrampolines -Walloca -Wvla -Warray-bounds=2 -Wimplicit-fallthrough=3 -Wtraditional-conversion -Wshift-overflow=2 -Wcast-qual -Wstringop-overflow=4 -Wconversion -Warith-conversion -Wlogical-op -Wduplicated-cond -Wduplicated-branches -Wformat-signedness -Wshadow -Wstrict-overflow=4 -Wundef -Wstrict-prototypes -Wswitch-default -Wswitch-enum -Wstack-usage=1000000 -Wcast-align=strict CONFIG_DEBUG_INFO_BTF_MODULES=
TARGET_MODULE := tsr

#$(TARGET_MODULE)-objs := source_1.o source_2.o … source_n.o
obj-m += $(TARGET_MODULE).o

MODULE_DIR = "/lib/modules/`uname -r`/build"

all: asm.o
	$(MAKE) $(CFLAGS) -C $(MODULE_DIR) M=$(PWD) modules

asm.o: asm.s
	as asm.s -o asm.o

clean:
	# Delete manually or asm.s is also deleted
	rm -f *.o *.ko
	rm -f .*.cmd Module.symvers modules.order $(TARGET_MODULE).mod $(TARGET_MODULE).mod.c
#	$(MAKE) $(CFLAGS) -C $(MODULE_DIR) M=$(PWD) clean

load:
	insmod ./$(TARGET_MODULE).ko

unload:
	rmmod ./$(TARGET_MODULE).ko
