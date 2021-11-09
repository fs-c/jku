.section .data
    encode_matrix: .byte 0b1101, 0b1011, 0b1000, 0b0111, 0b0100, 0b0010, 0b0001

.section .bss
    .equ READ_BUF_SIZE, 32768           # 2^15 (arbitrary)
    .lcomm READ_BUF_DATA, READ_BUF_SIZE

    .equ WRITE_BUF_SIZE, READ_BUF_SIZE*2
    .lcomm WRITE_BUF_DATA, WRITE_BUF_SIZE

.section .text
    # syscalls
    .equ SYS_OPEN,          2
    .equ SYS_READ,          0
    .equ SYS_WRITE,         1
    .equ SYS_CLOSE,         3
    .equ SYS_EXIT,          60

    # open() options
    .equ O_READ,            0
    .equ O_WRITE,           03101       # creat, wronly and trunc
    .equ O_PERMS,           0666        # demonic r/w for all users

    # read() status
    .equ EOF,               0           # end of file

    # stack positions of variables
    .equ ST_SIZE_RESERVE,   16          # space for local variables
    .equ ST_FD_IN,          -16         # input file descriptor
    .equ ST_FD_OUT,         -8          # output file descriptor

    # stack positions of arguments
    .equ ST_ARGC,           0
    .equ ST_ARGV_PROG,      8           # name of program
    .equ ST_ARGV_INPUT,     16          # input file name
    .equ ST_ARGV_OUTPUT,    24          # output file name

.global _start
_start:
    movq %rsp, %rbp                     # create new stack frame
    subq $ST_SIZE_RESERVE, %rsp         # reserve space for local variables

    cmpq $3, ST_ARGC(%rbp)              # check parameter count
    jne error                           # if != 3 it's invalid

open_files:
    # input file
    movq ST_ARGV_INPUT(%rbp), %rdi      # input filename pointer
    movq $O_READ, %rsi                  # open file for reading
    movq $SYS_OPEN, %rax
    syscall                             # open the file
    cmpq $0, %rax
    jl error                            # couldn't open file for reading

    movq %rax, ST_FD_IN(%rbp)           # save input file descriptor

    # output file
    movq ST_ARGV_OUTPUT(%rbp), %rdi     # output filename pointer
    movq $O_WRITE, %rsi                 # open file for writing
    movq $O_PERMS, %rdx                 # setup file permissions (if it doesn't exist)
    movq $SYS_OPEN, %rax
    syscall                             # open the file
    cmpq $0, %rax
    jl error                            # couldn't open file for writing

    movq %rax, ST_FD_OUT(%rbp)          # save output file descriptor

read_write_loop:
    # read an input chunk
    movq ST_FD_IN(%rbp), %rdi           # input file descriptor
    movq $READ_BUF_DATA, %rsi           # location to read into
    movq $READ_BUF_SIZE, %rdx           # (max) size of buffer
    movq $SYS_READ, %rax
    syscall                             # %rax contains number of bytes read

    cmpq $EOF, %rax                     # check for EOF
    je success                          # if EOF, we're done

    # loop through the buffer
    movq $0, %r12                       # loop counter
    movq %rax, %r13                     # number of bytes to loop through
encode_loop:
    cmpq %r13, %r12                     # check if we're done
    jge write_buffer                    # if so write out the completed buffer

    movb READ_BUF_DATA(, %r12), %dil    # get the byte to encode
    call encode_byte                    # encode the byte into a word
    movw %ax, WRITE_BUF_DATA(, %r12, 2) # save the encoding

    incq %r12                           # increment loop counter
    jmp encode_loop

write_buffer:
    # write the encoded chunk to disk (%r13 contains number of bytes/2)
    movq ST_FD_OUT(%rbp), %rdi          # output file descriptor
    movq $WRITE_BUF_DATA, %rsi          # location to write to
    movq %r13, %rdx                     # number of bytes to write (wrong at this point)
    addq %rdx, %rdx                     # double the number of bytes (now it's correct)
    movq $SYS_WRITE, %rax
    syscall

    cmpq %rdx, %rax                     # check if all bytes were written
    jne error

    jmp read_write_loop                 # start the r/w loop again

success:
    movq $0, %rbx                       # set up success status code for exit

    jmp close_handles

error:
    movq $1, %rbx                       # set up error status code for exit

    # the input and output files may be open or closed at this point but we will
    # attempt to close them anyways and just ignore any errors
    jmp close_handles

close_handles:
    # close input file
    movq ST_FD_IN(%rbp), %rdi           # input file descriptor
    movq $SYS_CLOSE, %rax
    syscall                             # close the file

    # close output file
    movq ST_FD_OUT(%rbp), %rdi          # output file descriptor
    movq $SYS_CLOSE, %rax
    syscall                             # close the file

exit:
    # expects %rbx to be set to the status code
    movq %rbx, %rdi                     # status code
    movq $SYS_EXIT, %rax                # exit syscall, uses status code
    syscall                             # bye

#
# function encode_byte
# encodes a byte (%dil) into a word (%ax)
#
encode_byte:
    pushq %rbx                          # save %rbx
    pushq %rdi                          # save %rdi

    andb $0xF, %dil                     # get the lower nibble
    call encode_nibble                  # encode the lower nibble
    movb %al, %bl                       # save the encoding

    popq %rdi                           # restore %rdi
    shr $4, %dil                        # get the upper nibble
    call encode_nibble                  # encode the upper nibble

    shlq $8, %rax                       # shift the encoded lower nibble into the upper byte
    addb %bl, %al                       # add encoding of the lower nibble

    popq %rbx                           # restore %rbx
    ret

#
# function encode_nibble
# encodes a nibble (4 bit, %rdi) into a byte (%rax)
#
encode_nibble:
    pushq %rbx                          # save rbx, used inside loop

    movq $0, %rax                       # set up return value

    movq $0, %rcx                       # loop counter
encode_nibble_loop:
    cmpq $7, %rcx                       # check if we're done
    jge encode_nibble_return

    shl $1, %rax                        # shift return value to the left

    movb %dil, %bl                      # set up loop local variable

    andb encode_matrix(, %rcx, 1), %bl  # logical and with the current encode matrix row
    popcnt %rbx, %rbx                   # count the number of bits set
    andq $1, %rbx                       # get least significant bit
    addq %rbx, %rax                     # add to return value

    incq %rcx                           # increment loop counter
    jmp encode_nibble_loop

encode_nibble_return:
	popq %rbx                           # restore rbx
    ret                                 # return to caller
