.data
array: .word 8, 6, 3, 4, 0, 1, 2, 7

.globl main

.text
main:
    addi t0, zero, 8    # t0 = array length
    addi t1, zero, 0    # n
    addi t2, zero, 1    # temp var for shift
    sra t0, t0, t2      # t0 = max iterations (sra by 1 to div by 2)
    la a0, array        # a0 = array
loop:
    addi a1, a0, 4      # a1 = a0 + 1

    lw t2, 0(a0)        # t2 = *a0
    lw t3, 0(a1)        # t3 = *a1
    sw t2, 0(a1)        # *a1 = t2
    sw t3, 0(a0)        # *a0 = t3

    addi a0, a0, 8      # a0 += 2

    addi t1, t1, 1      # n++
    blt t1, t0, loop    # continue loop if n < max iterations
end:

# bei ungerader laenge bleibt das letzte element unveraendert weil len/2
# bzw hier len >> 1 abrunden, der hoechste index ist also floor(length / 2) * 2,
# das letzte element wird nie betrachtet
