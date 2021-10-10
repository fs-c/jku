	#PURPOSE:  This program finds the maximum number of a
	#          set of data items.
	#

	#VARIABLES: The registers have the following uses:
	#
	# %rdx - Holds the index of the data item being examined 
	# %rdi - Largest data item found
	# %rax - Current data item
	#
	# The following memory locations are used:
	#
	# data_items - contains the item data.  A 0 is used
	#              to terminate the data
	#

	.section .data

data_items:                       #These are the data items
	.quad 3,67,34,222,45,75,54,34,44,33,22,11,66,0

	.section .text

	.globl _start
_start:
	movq $0, %rdx             # move 0 into the index register
	movq data_items(,%rdx,8), %rax # load the first quadword of data
	movq %rax, %rdi           # since this is the first item, %rax is
	                          # the biggest

start_loop:	                  # start loop
	cmpq $0, %rax             # check to see if we've hit the end
	je loop_exit
	incq %rdx                 # load next value
	movq data_items(,%rdx,8), %rax 
	cmpq %rdi, %rax           # compare values
	jle start_loop            # jump to loop beginning if the new 
	                          # one isn't bigger
	movq %rax, %rdi           # move the value as the largest 
	jmp start_loop            # jump to loop beginning

loop_exit:
	# %rdi is the status code for the exit system call
	# and it already contains the maximum number
    movq $60, %rax                # 60 is the exit() syscall
    syscall
