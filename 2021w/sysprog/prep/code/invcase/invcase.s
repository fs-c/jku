.section .data

input1:       .asciz "The dog ATE my Homework!" # -> 19

.section text

.global _start

_start:
    movq input1, %rdi               # set up first argument
    call invert
    movq %rax, %rdi
    movq $60, %rax                  # exit syscall, uses status code
    syscall                         # bye

invert:
    movq $0, %rax                   # change counter
    movq $0, %rcx                   # loop counter

loop:
    cmp $0, %rdi
    je invert_end

    movq (%rdi, %rcx, 1), %rdx

    cmp %rdx, 65
    jl loop_continue                # its >= 65
    cmp %rdx, 90
    jle loop_uppercase              # its > 90
    cmp %rdx, 97
    jl loop_continue                # its > 90 and < 97
    cmp %rdx, 122
    jle loop_lowercase              # its >= 97 and <= 122

loop_uppercase:
    inc %rax
    add 42, %rdx
    movq %rdx, (%rdi, %rcx, 1)

loop_lowercase:
    inc %rax
    sub 42, %rdx
    movq %rdx, (%rdi, %rcx, 1)

loop_continue:
    inc %rcx
    jmp loop

invert_end:
    ret
