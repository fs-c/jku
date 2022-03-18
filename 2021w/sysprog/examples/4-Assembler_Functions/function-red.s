	#PURPOSE:  This program calls a function
	#

	#PARAMETERS: 8 parameters, filles with the numbers 1-8, returns parameter 1
	#

	.section .text

	.globl _start
_start:
	mov $10,%r10		# Fill with data so we can recognize it later in memory
	mov $11,%r11
	mov $12,%r12
	mov $13,%rbx

	subq $8,%rsp		# Ensure stack alignment (we push 24 bytes; if 
				# aligned before we need to "add" 8 bytes more)
	pushq %r10       	# Save caller-safe registers
	pushq %r11
	movq $1,%rdi		# Store first parameter
	movq $2,%rsi		# Note: No parameters names appear in assembler!
	movq $3,%rdx
	movq $4,%rcx
	movq $5,%r8
	movq $6,%r9		# Store sixth parameter
	pushq $9		# Parameters are pushed on stack in reverse order!
	pushq $8
	pushq $7
	call doSomething
	addq $24,%rsp		# Clean up parameters from stack
	popq %r11		# Restore caller-safe registers
	popq %r10
	addq $8,%rsp		# Clean up alignment space
	cmpq $0,%rax		# Now check the return value
	je isZero		# If zero, jump over the next block
notZero:
	# Do something
	jmp end	
isZero:
	# Do something else
	# Fall through to end
end:
	movq %rax,%rdi		# Store function result as return code
	movq $60, %rax		# 60 is the exit() syscall
	syscall


doSomething:	
	pushq %rbp		# Store old base pointer
	movq %rsp,%rbp		# Create new base pointer
# No need for RSP adjustment, as less than 128 bytes
	pushq %rbx		# Save old value on stack
	pushq %r12		# R10 and R11 are caller-save!
	# ...
	movq 16(%rbp),%r12	# Access parameter 7
	movq %r12,-16(%rsp)	# Store it in local variable 2
	# ...
	movq %rdi,%rax		# Set return value
	# ...
	addq $10,%r10		# Change the registers we "use"
	addq $10,%r11
	addq $10,%r12
	addq $10,%rbx
	# ...
	popq %r12		# Restore old register values
	popq %rbx
	movq %rbp,%rsp		# Reset stack pointer always, even if not necessary!
	popq %rbp		# Restore old base pointer
	ret			# Return to calling function
