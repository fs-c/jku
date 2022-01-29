.section .data

.section .text
.globl _start
_start:
	movq  $4,%rdi    # The factorial takes one argument - the 
	                 # number we want a factorial of.  So, it
	                 # gets put into RDI
	call  factorial  # Run the factorial function
	movq  %rax,%rdi  # Factorial returns the answer in %rax, but 
	                 # we want it in %rdi to send it as our exit 
	                 # status
	movq  $60,%rax   # Call the kernel's exit function
	syscall

