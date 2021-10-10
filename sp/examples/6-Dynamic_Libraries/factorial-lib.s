.section .data
.section .text

.globl factorial
.type factorial,@function
factorial:
	pushq %rbp       # Standard function stuff - we have to 
	                 # restore %rbp to its prior state before 
	                 # returning, so we have to push it.
	movq  %rsp,%rbp  # This is because we don't want to modify
	                 # the stack pointer, so we use %rbp.

check_base_case0:
	cmpq $0,%rdi        # If the number is 0, we return 1 
	jne  check_base_case1
	movq $1,%rax        # Prepare return value
	jmp  end_factorial

check_base_case1:
	cmpq $1,%rdi        # If the number is 1, that is our base 
	                    # case, and we simply return 1
	jne  do_recursive
	movq $1,%rax        # Prepare return value
	jmp  end_factorial

do_recursive:
	pushq %rdi          # Save original value (function
	                    # might overwrite it - caller save!)
	decq  %rdi          # Decrease the value
	call  factorial@PLT # Recursively call factorial
	                    # Add '@PLT' to force generation of PIC
	                    # (Position Independent Code), which
	                    # is necessary for shared libraries.
	popq  %rdi          # %rax has the return value, so we 
	                    # reload our parameter into %rdi
	imulq %rdi,%rax     # Multiply that by the result of the
	                    # last call to factorial (in %rax)
	                    # the result is stored in %rax, which 
	                    # is good since that's where return 
	                    # values go.
end_factorial:
	movq  %rbp,%rsp     #standard function return stuff - we
	popq  %rbp          #have to restore %ebp and %esp to where
	                    #they were before the function started
	ret                 #return from the function
