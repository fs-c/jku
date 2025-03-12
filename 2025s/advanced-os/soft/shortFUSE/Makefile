CFLAGS = -Werror -Wall -Wextra -Wformat=2 -Wformat-overflow=2 -Wformat-truncation=2 -Wformat-security -Wnull-dereference -Wstack-protector -Wtrampolines -Walloca -Warray-bounds=2 -Wimplicit-fallthrough=3 -Wtraditional-conversion -Wshift-overflow=2 -Wcast-qual -Wstringop-overflow=4 -Wconversion -Warith-conversion -Wlogical-op -Wduplicated-cond -Wduplicated-branches -Wformat-signedness -Wshadow -Wstrict-overflow=4 -Wundef -Wstrict-prototypes -Wswitch-default -Wswitch-enum -Wcast-align=strict -std=gnu11
# -Wstack-usage=1000000 -> Complains about sf_read and getEntry, that the variable-sized arrays might be too large. 
# Even if they are guaranteed not to be (inference weakness)
# -Wvla -> we do use variable-length arrays in a few cases for simplicity
# -Wpedantic -> complains about uint64_t child_entries[]; in directory_entry
FUSE_LIB=$(shell pkg-config fuse3 --cflags --libs)

all: shortFUSE test

test: test.c
	gcc $(CFLAGS) -o test test.c

shortFUSE:
	gcc $(CFLAGS) -g -O0 shortFUSE.c -I/usr/include/fuse3 -L/usr/lib/x86_64-linux-gnu -lfuse3 -lpthread -o shortFUSE  

clean:
	rm -f shortFUSE test
	
run:
	./run.sh

runtest:
	./testsuite/test.sh ./fuse
