make

./matrixmult ref-data/input/$1 > $1.actual

cmp -b $1.actual ref-data/output/$2

make clean
