#!/bin/bash

. $(dirname $0)/testlib.sh

testdir="$basepath/$testname"

# cleanup
rm -rf "$testdir"
mkdir -p "$testdir"

echo -en "hello" >> $testdir/foo
chmod oug+rwx "$testdir/foo"
[[ $(cat $testdir/foo) == "hello" ]]

echo -en " shortFUSE" >> $testdir/foo
[[ $(cat $testdir/foo) == "hello shortFUSE" ]]

# cleanup
rm -rf "$testdatadir"
rm -rf "$testdir"
[[ ! -d $testdir ]]
