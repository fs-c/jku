make

./matrixmult ref-data/input/100x100.in > 100x100.in.out
./matrixmult ref-data/input/10x10.in > 10x10.in.out
./matrixmult ref-data/input/200x200.in > 200x200.in.out
./matrixmult ref-data/input/30x30.in > 30x30.in.out
./matrixmult ref-data/input/double_sign.in > double_sign.in.out
./matrixmult ref-data/input/incompatible_sizes.in > incompatible_sizes.in.out
./matrixmult ref-data/input/input.txt > input.txt.out
./matrixmult ref-data/input/large_number.in > large_number.in.out
./matrixmult ref-data/input/leading_zero.in > leading_zero.in.out
./matrixmult ref-data/input/missing_number.in > missing_number.in.out
./matrixmult ref-data/input/random_white_spaces.in > random_white_spaces.in.out
./matrixmult ref-data/input/sum_of_squares.in > sum_of_squares.in.out
./matrixmult ref-data/input/too_big_number.in > too_big_number.in.out
./matrixmult ref-data/input/wrong_size.in > wrong_size.in.out
./matrixmult ref-data/input/zero_matrix.in > zero_matrix.in.out

diff ref-data/output/100x100.out 100x100.in.out
diff ref-data/output/10x10.out 10x10.in.out
diff ref-data/output/200x200.out 200x200.in.out
diff ref-data/output/30x30.out 30x30.in.out
diff ref-data/output/double_sign.out double_sign.in.out
diff ref-data/output/incompatible_sizes.out incompatible_sizes.in.out
diff ref-data/output/input.tout input.txt.out
diff ref-data/output/large_number.out large_number.in.out
diff ref-data/output/leading_zero.out leading_zero.in.out
diff ref-data/output/missing_number.out missing_number.in.out
diff ref-data/output/random_white_spaces.out random_white_spaces.in.out
diff ref-data/output/sum_of_squares.out sum_of_squares.in.out
diff ref-data/output/too_big_number.out too_big_number.in.out
diff ref-data/output/wrong_size.out wrong_size.in.out
diff ref-data/output/zero_matrix.out zero_matrix.in.out

make clean
