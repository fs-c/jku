#
#PURPOSE:  This program writes the message "hello world" and
#          exits
#

.section .data
helloworld:
	.ascii "hello world\n\0"

.section .text
.globl _start
_start:
	movq $helloworld,%rdi	# Store address in first parameter
	xorq %rax,%rax		# Clear RAX (no floating point parameters
				# this is a vararg function)
				# We didn't use the stack, so it should
				# remain 16-Byte aligned from _start
	call printf

	movq $0,%rdi		# Terminate program
	call exit
