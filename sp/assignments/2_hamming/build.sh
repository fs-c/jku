mkdir out && cd out

as ../encode.s --gstabs+
ld a.out -o ../encode.out

cd .. && rm -rf out