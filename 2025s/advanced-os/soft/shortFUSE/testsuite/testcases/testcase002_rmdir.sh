#!/bin/bash

. $(dirname $0)/testlib.sh

testdir="$basepath/$testname"

# cleanup
rm -rf "$testdir"

mkdir -p "$testdir/A/AA/AAA/AAAA"
mkdir -p "$testdir/A/AA/AAA/AAAB"
mkdir -p "$testdir/A/AA/AAA/AAAC"
mkdir -p "$testdir/A/BB/ABB/ABBA"
mkdir -p "$testdir/A/BB/ABB/ABBB"
[[ -d $testdir/A/AA/AAA/AAAA ]]
[[ -d $testdir/A/AA/AAA/AAAB ]]
[[ -d $testdir/A/AA/AAA/AAAC ]]
[[ -d $testdir/A/BB/ABB/ABBA ]]
[[ -d $testdir/A/BB/ABB/ABBB ]]

rm -rf "$testdir/A/AA/AAA/AAAB"
[[ -d $testdir/A/AA/AAA/AAAA ]]
[[ ! -d $testdir/A/AA/AAA/AAAB ]]
[[ -d $testdir/A/AA/AAA/AAAC ]]
[[ -d $testdir/A/BB/ABB/ABBA ]]
[[ -d $testdir/A/BB/ABB/ABBB ]]

rm -rf "$testdir/A/BB/ABB"
[[ -d $testdir/A/AA/AAA/AAAA ]]
[[ ! -d $testdir/A/AA/AAA/AAAB ]]
[[ -d $testdir/A/AA/AAA/AAAC ]]
[[ ! -d $testdir/A/BB/ABB/ABBA ]]
[[ ! -d $testdir/A/BB/ABB/ABBB ]]
[[ ! -d $testdir/A/BB/ABB ]]

rm -rf $testdir/A/AA
[[ ! -d $testdir/A/AA/AAA/AAAA ]]
[[ ! -d $testdir/A/AA/AAA/AAAB ]]
[[ ! -d $testdir/A/AA/AAA/AAAC ]]
[[ ! -d $testdir/A/AA/AAA ]]
[[ ! -d $testdir/A/AA ]]
[[ ! -d $testdir/A/BB/ABB/ABBA ]]
[[ ! -d $testdir/A/BB/ABB/ABBB ]]
[[ ! -d $testdir/A/BB/ABB ]]
[[ -d $testdir/A/BB ]]

# cleanup
rm -rf "$testdir"
[[ ! -d $testdir ]]
