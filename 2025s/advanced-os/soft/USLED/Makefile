MAKE_FLAGS = CONFIG_DEBUG_INFO_BTF_MODULES=
CFLAGS = -Werror -Wall -Wextra -Wpedantic -Wformat=2 -Wformat-overflow=2 -Wformat-truncation=2 -Wformat-security -Wnull-dereference -Wstack-protector -Wtrampolines -Walloca -Wvla -Warray-bounds=2 -Wimplicit-fallthrough=3 -Wtraditional-conversion -Wshift-overflow=2 -Wcast-qual -Wstringop-overflow=4 -Wconversion -Warith-conversion -Wlogical-op -Wduplicated-cond -Wduplicated-branches -Wformat-signedness -Wshadow -Wstrict-overflow=4 -Wundef -Wstrict-prototypes -Wswitch-default -Wswitch-enum -Wstack-usage=1000000 -Wcast-align=strict
TARGET_MODULE:=kmleds

#$(TARGET_MODULE)-objs := source_1.o source_2.o … source_n.o
obj-m += $(TARGET_MODULE).o

MODULE_DIR = "/lib/modules/`uname -r`/build"

all: leds kmleds

leds: leds.c
	gcc $(CFLAGS) -o leds leds.c

kmleds: kmleds.c
	$(MAKE) $(CFLAGS) $(MAKE_FLAGS) -C $(MODULE_DIR) M=$(PWD) modules

clean:
	rm -f leds leds.o
	$(MAKE) $(CFLAGS) $(MAKE_FLAGS) -C $(MODULE_DIR) M=$(PWD) clean
	
load:
	insmod ./$(TARGET_MODULE).ko

unload:
	rmmod ./$(TARGET_MODULE).ko
