#!/bin/bash

. $(dirname $0)/testlib.sh
testdir="$basepath/$testname"

# cleanup
rm -rf "$testdir"
mkdir -p "$testdir"

# create
touch "$testdir/foo"

# allow all
chmod oug+rwx "$testdir/foo"
# re-check mod
mod="$(ls -l "$testdir/foo" | cut -d' ' -f1)"
[[ $mod == "-rwxrwxrwx" ]]
# test mod
echo "boo" > $testdir/foo

chmod oug-rwx "$testdir/foo"
# re-check mod
mod="$(ls -l "$testdir/foo" | cut -d' ' -f1)"
[[ $mod == "----------" ]]
# test mod
if (echo "boo" > $testdir/foo) 2>/dev/null ; then
	exit 1
fi

# cleanup
rm -rf "$testdir"

[[ ! -d $testdir ]]
