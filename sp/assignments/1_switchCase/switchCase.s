.section .data
input1:       .asciz "The dog ATE my Homework!" # -> 19
input2:       .asciz ""	# -> 0
input3:       .asciz "#!$"	# -> 0

.section .text

.global _start
_start:
    movq $0, %rbx                   # change counter
    movq $0, %rcx                   # loop counter

loop:
    movb input1(, %rcx, 1), %al     # current char

    cmpb $0, %al                    # check if terminator is reached
    je end

    cmpb $'A', %al
    jb loop_end                     # < A, ignore
    cmpb $'Z', %al
    jbe loop_convert                # >= A and <= Z

    cmpb $'a', %al
    jb loop_end                     # > Z but < a, ignore
    cmpb $'z', %al
    ja loop_end                     # > z, ignore

loop_convert:
    xorb $32, input1(, %rcx, 1)     # convert case in-place by toggling 6th bit

    incq %rbx                       # increment change counter

loop_end:
    incq %rcx                       # increment loop counter
    jmp loop

end:
    movq %rbx, %rdi                 # status code
    movq $60, %rax                  # exit syscall, uses status code
    syscall                         # bye
