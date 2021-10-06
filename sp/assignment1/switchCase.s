.section .data
input1:       .asciz "The dog ATE my Homework!" # -> 19
input2:       .asciz ""	# -> 0
input3:       .asciz "#!$"	# -> 0

.section .text
# ---------------------------------
# "Inverts" the case of a string: lowercase is changed to uppercase, uppercase to
# lowercase, and everything else stays the same. The conversion is in-place.
# It returns the number of characters that were inverted
# Example: "The Dog" -> "tHE dOG" returns 6
# Example: "" -> "" returns 0
# Example: "#!$" -> "#!$" returns 0
# ---------------------------------

.global _start
_start:
    movq $0, %rcx                   # loop counter
    movq $0, %rdx                   # change counter
    
loop:
    movq input1(, %rcx, 8), %rax    # current character

    cmpq $0, %rax                   # check if last character
    je end

    cmpq $'a', %rax                 # check if upper- or lowercase
    jge loop_lower
    movq $32, %rbx
loop_lower:
    movq $-32, %rbx

    addq %rax, %rbx
    incq %rdx

    incq %rcx                       # increment loop counter
    jmp loop                        # and restart the loop

end:
    movq %rdx, %rdi                 # status code
    movq $60, %rax                  # exit syscall, uses status code
    syscall                         # bye
