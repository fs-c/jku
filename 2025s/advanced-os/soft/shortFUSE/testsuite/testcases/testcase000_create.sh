#!/bin/bash

. $(dirname $0)/testlib.sh

testfile="$basepath/$testname"

# cleanup
rm -rf "$testfile"

touch "$testfile"

# check
if ! [[ -f $testfile ]] ; then
	exit 1
fi

# cleanup
rm -rf "$testfile"
[[ ! -f $testdir ]]
