mkdir out && cd out

as ../switchCase.s --gstabs+
ld a.out -o ../switchCase.out

cd .. && rm -rf out