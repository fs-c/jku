	.section .data
	.section .text

	.globl _start
_start:
	call allocate_init # Initialize memory manager
	movq $8,%rdi       # Alloc takes size as argument
	call allocate      # Allocate space for one quad (64 bits)
	cmpq $0,%rax       # Check success
	jne  use_memory
	movq $-1,%rdi      # Return -1 on error
	jmp  end
use_memory:
	movq $8,(%rax)     # Write immediate 8 into the allocated space
	movq (%rax),%rdi   # Read the value from memory and load it into %rdi
free_memory:	           # Free all used memory
	movq %rax,%rdi
	call deallocate    # Everything reserved should (must) be freed again
end:
	movq $60,%rax      # Call the kernel's exit function
                           # Return value should be 8
	syscall

