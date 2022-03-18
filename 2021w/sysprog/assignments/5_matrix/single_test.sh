make

./matrixmult ref-data/input/$1 &> $1.actual

diff -ys $1.actual ref-data/output/$2

make clean
