CFLAGS = -Werror -Wall -Wextra -Wpedantic -Wformat=2 -Wformat-overflow=2 -Wformat-truncation=2 -Wformat-security -Wnull-dereference -Wstack-protector -Wtrampolines -Walloca -Wvla -Warray-bounds=2 -Wimplicit-fallthrough=3 -Wtraditional-conversion -Wshift-overflow=2 -Wcast-qual -Wstringop-overflow=4 -Wconversion -Warith-conversion -Wlogical-op -Wduplicated-cond -Wduplicated-branches -Wformat-signedness -Wshadow -Wstrict-overflow=4 -Wundef -Wstrict-prototypes -Wswitch-default -Wswitch-enum -Wstack-usage=1000000 -Wcast-align=strict CONFIG_DEBUG_INFO_BTF_MODULES=
TARGET_MODULE := macro

#$(TARGET_MODULE)-objs := source_1.o source_2.o … source_n.o
obj-m += $(TARGET_MODULE).o
macro-objs := macro_main.o

MODULE_DIR = "/lib/modules/`uname -r`/build"

all:
	$(MAKE) $(CFLAGS) -C $(MODULE_DIR) M=$(PWD) modules

clean:
	$(MAKE) $(CFLAGS) -C $(MODULE_DIR) M=$(PWD) clean

load:
	/sbin/insmod ./$(TARGET_MODULE).ko

unload:
	/sbin/rmmod ./$(TARGET_MODULE).ko

