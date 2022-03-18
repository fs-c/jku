mkdir out && cd out

as  --gstabs+ ../invcase.s
ld a.out -o ../invcase.o

cd .. && rm -rf out