#!/bin/bash

. $(dirname $0)/testlib.sh

testdir="$basepath/$testname"

# cleanup
rm -rf "$testdir"
mkdir "$testdir"

# check
if ! [[ -d $testdir ]] ; then
	exit 1
fi

# cleanup
rm -rf "$testdir"
[[ ! -d $testdir ]]
