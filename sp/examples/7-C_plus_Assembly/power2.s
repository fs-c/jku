	# PURPOSE:  Program to illustrate how functions work

	#

	# The function does not have any global data,
	# so the data section doesn't contain anything.
	.section .data 

	.section .text



	# PURPOSE:  This function is used to compute
	#           the value of a number raised to
	#           a power.
	#
	# INPUT:    First argument - the base number
	#           Second argument - the power to 
	#                            raise it to
	#
	# OUTPUT:   Will give the result as a return value
	#
	# NOTES:    The power must be 0 or greater
	#
	# VARIABLES: 
	#           %rdi - holds the base number
	#           %rsi - holds the power
	#           %rax - holds the current result
	#
	#


	.globl power
	.type power, @function
power:
	pushq %rbp           # Save old base pointer
	movq %rsp, %rbp      # Make stack pointer the base pointer

	movq %rdi, %rax      # Store current result

	cmpq $0, %rsi        # If the power is 0, then we return 1
	jne power_loop_start
	movq $1, %rax        # Store result
	jmp end_power

power_loop_start:
	cmpq $1, %rsi        # If the power is 1, we are done
	je end_power
	imulq %rdi, %rax     # Multiply the current result by
	                     # the base number

	decq %rsi            # Decrease the power
	jmp power_loop_start # Loop for next power

end_power:
	movq %rbp, %rsp      # Restore stack pointer
	popq %rbp            # Restore base pointer
	ret
