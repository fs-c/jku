#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e

if [[ -z $1 ]] ; then
	echo "Usage: $0 <mountpoint>"
	exit 1
fi
basepath="$1"

ret=0
for testcase in $(dirname $0)/testcases/testcase???_*.sh ; do
	echo -en "$(basename $testcase): "
	if $testcase $basepath ; then
		echo "OK"
	else
		echo "FAIL"
        ret=1
	fi
done

exit $ret
