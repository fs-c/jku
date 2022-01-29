    #PURPOSE: Simple program that demonstrates
    #         various memory accesses
    #

    #INPUT:   none
    #

    #OUTPUT:  none
    #

    #VARIABLES:
    #         %rsi 			address from where to retrieve the data
    #         %rdi/%di%dil  the retrieved data 
	#         %rax,%rbc,%rcs,%rdx 	registers for holding offset/indices/...
    #
    
.section .data
    data_items: .byte 0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08

.section .text
    
.globl _start
    
_start:
    movq $0,%rdi
    movq $data_items,%rsi
    movq %rsi,%rdi          # No memory access, we copy a register: memory address of data items, e.g. 0x6001CE

    movq $0,%rdi
    movq $data_items,%rsi
    movq (%rsi),%rdi        # Indirect memory access: 0x0807060504030201

    movq $0,%rdi
    movq data_items,%rdi    # Direct memory access: 0x0807060504030201

    movq $0,%rdi
    movq $data_items,%rsi
    movb (%rsi),%dil        # Indirect memory access, retrieve single byte only: 0x01

    movq $0,%rdi
    movq $data_items,%rsi
    movb 1(%rsi),%dil       # "Base pointer" access, retrieve single byte only: 0x02

    movq $0,%rdi
    movq $data_items,%rsi
    movw (%rsi),%di         # Indirect memory access, retrieve word (=2 bytes): 0x0201

    movq $0,%rdi
    movq $data_items,%rsi
    movw 1(%rsi),%di        # "Base pointer" access, retrieve word (=2 bytes): 0x0302

    movq $0,%rdi
    movq $data_items,%rsi
    movw 2(%rsi),%di        # "Base pointer" access, retrieve word (=2 bytes): 0x0403

    movq $0,%rdi
    movq $1,%rbx
    movw data_items(,%rbx,2),%di    # Indexed access, retrieve word at offset 1*2: 0x0403

    movq $0,%rdi
    movq $1,%rbx
    movq $3,%rcx
    movw data_items(%rcx,%rbx,2),%di    # Indexed access, retrieve word at offset 3+1*2: 0x0706
    
    movq $0,%rdi
    movq $1,%rbx
    movq $3,%rcx
    # Do the same "manually"
    movq %rbx,%rax          # Get content of register RBX
    shlq $1,%rax            # Multiply it by 2
    addq %rcx,%rax          # Add content of register RCX
    addq $data_items,%rax   # Add immediate value/offset
    movw (%rax),%di         # Retrieve memory content from 0x6001D3: 0x0706 

    movq $0,%rdi
    movq $1,%rbx
    movq $3,%rcx
    # Access via precalculated address
    leaq data_items(%rcx,%rbx,2),%rax    # Calculate address into RAX: 0x6001D3
    movw (%rax),%di         # Retrieve word from precalulated address: 0x0706
    # We cannot do this otherwise... data_items+RCX+RBX*2+RDX is too complex
    movq $1,%rdx
    movw (%rax,%rdx,1),%di  # Retrieve word indexed from precalulated address: 0x0807


    movq $60, %rax          # Terminate program
    movq $0, %rdi
    syscall
