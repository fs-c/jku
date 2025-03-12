#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e

if [[ -z $1 ]] ; then
	echo "Usage: $0 <mountpoint>"
	exit 1
fi

testname="$(basename $0)"
testname="${testname/.sh/}"
basepath="$1"
