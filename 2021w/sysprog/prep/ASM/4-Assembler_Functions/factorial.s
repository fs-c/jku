	# PURPOSE - Given a number, this program computes the
	#           factorial.  For example, the factorial of
	#           3 is 3 * 2 * 1, or 6.  The factorial of
	#           4 is 4 * 3 * 2 * 1, or 24, and so on.
	#

	# This program shows how to call a function recursively.
	
	# WARNING: THIS PROGRAM DOES NOT FOLLOW THE C CALLING CONVENTION
	#          WHEN IT COMES TO SAVING AND RESTORING REGISTERS
	
	.section .data

	# This program has no global data

	.section .text

	.globl _start
	.globl factorial # this is not needed unless we want to share
	                 # this function among other programs
_start:
	movq $4,%rdi     # The factorial takes one argument - the 
	                 # number we want a factorial of (4 -> 24).
	call  factorial  # run the factorial function
	movq  %rax,%rdi  # factorial returns the answer in %rax, but 
	                 # we want it in %rdi to send it as our exit status
	movq  $60,%rax   # call the kernel's exit function
	syscall


	# This is the actual function definition
	.type factorial,@function
factorial:
	pushq %rbp       # standard function stuff - we have to 
	                 # restore %rbp to its prior state before 
	                 # returning, so we have to push it
	movq  %rsp,%rbp  # This is because we don't want to modify
	                 # the stack pointer, so we use %rbp.
	pushq %rbx       # Save RBX (used for multiplication)
                         # Note: We could easily use e.g. R11 to
                         # avoid needing the stack!

check_base_case0:
	movq $1,%rax
	cmpq $0,%rdi        # If the number is 0, we return 1 
	je end_factorial

check_base_case1:
	cmpq  $1,%rdi       # If the number is 1, that is our base 
	                    # case, and we simply return (1 is 
	                    # already in %rax as the return value)
	je end_factorial    
	pushq %rdi          # save our own parameter for later
	decq  %rdi          # decrease the value
	call  factorial     # call factorial
        popq %rbx           # retrieve our own parameter
	imulq %rbx,%rax     # multiply it by the result of the last
	                    # call to factorial (in %rax); the answer
	                    # is stored in %rax, which is good since 
	                    # that's where return values go.
end_factorial:
	popq  %rbx          # restore old value
	movq  %rbp,%rsp     # standard function return stuff - we
	popq  %rbp          # have to restore %rbp and %rsp to where
	                    # they were before the function started
	ret                 # return from the function 
	

