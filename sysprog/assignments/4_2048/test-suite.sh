make clean
make

DIFF="diff -y --suppress-common-lines"
GAME="valgrind ./game_2048"

$GAME in=ref-data/input/input.txt out=output.txt seed=100
$DIFF ref-data/output/output.txt output.txt

$GAME in=ref-data/input/input_win.txt out=output.txt
$DIFF ref-data/output/output_win.txt output.txt

$GAME in=ref-data/input/input_fail.txt out=output.txt seed=404
$DIFF ref-data/output/output_fail.txt output.txt

$GAME in=ref-data/input/input_cont.txt out=output.txt seed=666
$DIFF ref-data/output/output_cont.txt output.txt

$GAME in=ref-data/input/input_other.txt out=output.txt seed=123
$DIFF ref-data/output/output_other.txt output.txt

make clean