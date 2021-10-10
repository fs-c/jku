	# PURPOSE - Given two numbers, n and k, this program computes the
	#           binomial coefficient "n over k".
	# (n over 0) = (n over n) = 1
	# (n over k) = (n - 1 over k - 1) + (n - 1 over k)

	# This program shows how to call a function recursively. 

	# WARNING: THIS PROGRAM DOES NOT FOLLOW THE C CALLING CONVENTION
	#          WHEN IT COMES TO SAVING AND RESTORING REGISTERS

	.section .data

	# This program has no global data

	.section .text

	.globl _start
	.globl binom     # this is not needed unless we want to share
	                 # this function among other programs
_start:
	# binom takes two arguments: We calculate 5 over 3 here 
        # the result should be 10
	movq  $3,%rsi    # first we store k (2nd param)
	movq  $5,%rdi    # then we store n  (1st param)
	call  binom      # run binom 
	movq  %rax,%rdi  # binom returns the answer in %rax, but we
	                 # want it in %rdi to send it as our exit status
	movq  $60,%rax   # call the kernel's exit function
	syscall


	# This is the actual function definition
	.type binom,@function
	                     # RDI = n, RSI = k
binom:
	pushq %rbp           # standard function stuff - we have to 
	                     # restore %rbp to its prior state before 
	                     # returning, so we have to push it
	movq  %rsp,%rbp      # This is because we don't want to modify
	                     # the stack pointer, so we use %rbp.
	                     # 8(%rbp) holds the return address

	subq $32,%rsp        # get room for local n, local k and
	                     # result of first recursive call
	                     # Additional 8 Bytes for stack alignment
	                     # in recursive calls

check_base_case1:
	cmpq $0,%rsi         # If k is 0, we return 1 
	jne check_base_case2
	movq $1,%rax
	jmp end_binom

check_base_case2:
	cmpq  %rdi,%rsi     # If n = k, we return 1 
	jne general_case 
	movq $1,%rax
	jmp end_binom    

general_case:
	# Note: Parameters are passed in registers in 64 Bit,
        # so we do not have a "backup copy" on our stack!
	movq  %rdi, -8(%rbp) # save n 
	movq  %rsi,-16(%rbp) # save k
	decq  %rdi           # decrease n
	decq  %rsi           # decrease k
	# first recursive call: (n - 1 over k - 1)
	call  binom          # recursive call
	movq %rax,-24(%rbp)  # save value of first recursive call
	movq  -8(%rbp),%rdi  # restore n 
	movq -16(%rbp),%rsi  # restore k
	decq %rdi            # decrease n
	# second recursive call: (n - 1 over k)
	call  binom          # recursive call
	# %rax holds result of second recursive call
	addq -24(%rbp),%rax  # compute sum of recursive calls = result
	# %rax holds result 

end_binom:
	movq  %rbp,%rsp      # standard function return stuff - we
	popq  %rbp           # have to restore %ebp and %esp to where
	                     # they were before the function started
	ret                  # return from the function 
	

