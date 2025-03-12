#!/bin/bash

. $(dirname $0)/testlib.sh

testdir="$basepath/$testname"

# create test data
testdatadir=$(mktemp -d --suffix "_testname")
dd if=/dev/urandom of="$testdatadir/small09" bs=9 count=1 >/dev/null 2>&1 # 9 bytes
dd if=/dev/urandom of="$testdatadir/small10" bs=10 count=1 >/dev/null 2>&1 # 10 bytes
dd if=/dev/urandom of="$testdatadir/small11" bs=11 count=1 >/dev/null 2>&1 # 11 bytes
dd if=/dev/urandom of="$testdatadir/med" bs=4096 count=1 >/dev/null 2>&1 # 4KB
dd if=/dev/urandom of="$testdatadir/big" bs=4096 count=4 >/dev/null 2>&1 # 16KB

# cleanup
rm -rf "$testdir"
mkdir -p "$testdir"

# create and check
for size in small09 small10 small11 med big ; do
	# copy
	cp "$testdatadir/$size" "$testdir/$size"
	# check existence
	[[ -f "$testdir/$size" ]]
	# check data
	diff "$testdatadir/$size" "$testdir/$size"
done

# re-check
for size in small09 small10 small11 med big ; do
	mkdir -p "$testdir"
	# check existence
	[[ -f "$testdir/$size" ]]
	# check data
	diff "$testdatadir/$size" "$testdir/$size"
done

# delete med
rm "$testdir/med"
[[ ! -f "$testdir/med" ]]

# re-check small med
for size in small09 small10 small11 big ; do
	# check existence
	[[ -f "$testdir/$size" ]]
	# check data
	diff "$testdatadir/$size" "$testdir/$size"
done

# cleanup
rm -rf "$testdatadir"
rm -rf "$testdir"
[[ ! -d $testdir ]]
