#!/bin/bash

# If the program crashed, the filesystem will still be mounted -> unmount for next test
fusermount -qu fuse

# Create directory for mounting
mkdir -p fuse

# Start filesystem - with full memory checks to verify against leaks, accessing uninitalized data etc
echo "Press Ctrl-C to terminate"
# -f ... Remain in foreground
# -s ... run single-threaded
valgrind -q --leak-check=full ./shortFUSE -f -s $(dirname $0)/fuse
# The next allows access also by other users
#valgrind -q --leak-check=full ./shortFUSE -f -s $(dirname $0)/fuse -o allow_other

# Remove directory used for mounting
rmdir fuse
