.globl main

.text
main:
    li a0, 0x40400000   # 3.0
    li a1, 0x3d400000   # 0.046875   

    jal function
    
    addi a0, zero, 10
    ecall

function:
    fmv.s.x f0, a0      # f0 = 3.0
    fmv.s.x f1, a1      # f1 = 0.046875
    addi t0, zero, 5    # t0 = 5
    fcvt.s.x f2, t0     # f2 = 5.0
    addi t0, zero, 2    # t0 = 2
    fcvt.s.x f3, t0     # f3 = 2.0
    addi t0, zero, 0    # t0 = 0
loop:                   # do {
    fadd.s f2, f2, f3   #   f2 += 2.0
    fdiv.s f0, f0, f2   #   f0 /= 5.0
    fmul.s f4, f0, f2   #   f4 = f0 * f2
    flt t1, f4, f1      #   t1 = f4 < f1
    beq t0, t1, loop    # } while (t0 == t1 => f4 >= f1)
end:
    jr ra