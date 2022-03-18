	# PURPOSE - Print strings to the console, including the first parameter
	# But now use string instructions to calculate the length of the parameter

	.section .bss
	.equ MAX_LEN,9
	.lcomm BUFFER,MAX_LEN+1

	.section .data

	prefix: .ascii "Hello \0"	# Must be terminated manually
	.set prefix_len,.-prefix	# Calculate length as current address minus start address of string

	postfix: .asciz ", you are looking good"	# Automatically terminated
	.set postfix_len,.-postfix

	error: .string "Program parameter(s) incorrect: <name> <count>\n"	# Automatically terminated
	.set error_len,.-error

	.section .text


	.globl _start

_start:
	movq %rsp,%rbp
	# Check parameter count
	cmpl $3,0(%rbp)
	jne print_error 
	
	# Print prefix	
	movq $1,%rdi		# File descriptor of STDOUT
	movq $prefix,%rsi	# Print prefix
	movq $prefix_len,%rdx	# Length of string
	movq $1,%rax		# Write to stream
	syscall

	# Print parameter 1
	movq 16(%rbp),%rdi	# Store start address of string
	movq $-1,%rcx		# Initialize with maximum possible length
	cld			# Set direction to for-/upward
	movb $0,%al		# Set the value to look for
	repne scasb		# Repeat while not equal a scan for %al
	# Calculate length: -1(=4.294.967.295)-current value-1 or ecx=-length-2
	# Option A: negl %ecx, decl %ecx, decl %ecx
	# Option B: negl %ecx, decl %ecx is the same as notl %ecx (2-complement!)
	notq %rcx		# Invert bits
	decq %rcx		# Decrement by one
	movq %rcx,%rdx		# Store as length

	movq $1,%rdi		# File descriptor of STDOUT
	movq 16(%rbp),%rsi	# Print parameter 1
	# RDX (=Length of string) has been calculated above!
	movq $1,%rax		# Write to stream
	syscall

        # Print postfix
        movq $1,%rdi            # File descriptor of STDOUT
        movq $postfix,%rsi      # print postfix
        movq $postfix_len,%rdx  # Length of string
        movq $1,%rax            # Write to stream
        syscall

	# Print as many exclamation marks as the parameter 2 tells us
	# Limit it to 10, as this is the maximum with one digit
	movq 24(%rbp),%rcx	# Get address of count
	movq (%rcx),%rdx	# Retrieve actual word
	cmpb $0,%dh		# Check the second byte really is zero
	jne print_error
	cmpb $0,%dl		# Check the first byte it NOT zero
	je print_error
	# Careful: We don't check the range here ('0'...'9')!
	subb $'0',%dl		# Convert from character to number
	movq $0,%rcx		# Create correct ECX
	movb %dl,%cl
	pushq %rcx		# Store it - we will need it later as length for printing

	# Create string of exclamation marks
	cld			# Set direction upward
	movq $BUFFER,%rdi	# Set target address
	movb $'!',%al		# The character to print
	rep stosb		# Repeatedly store the byte in AL
	movb $'\n',(%rdi)	# Add line break
	# Note: We don't need zero-termination here, as we explicitly set the length
	
	# Print exclamation marks
	movq $1,%rdi		# File descriptor of STDOUT
	movq $BUFFER,%rsi	# Print exclamation marks
	popq %rdx		# Retrieve length from stack
	incq %rdx		# Adjust for linebreak
	movq $1,%rax		# Write to stream
	syscall

	jmp program_end

print_error:
	andq $-16,%rsp		# Stack must be 16-byte aligned for call!
	# Not really necessary here, as is already aligned from _start
	# and we didn't change it since - but anyway to show how
	# Normally: 8 byte RIP + 8 bytes Old-RBP --> Stays aligned!
	# -16 = 0xf...fff0 -> Last 4 bits will be zeroed 
	# Remember: Stack grows "down" to lower addresses!
	movq $error,%rdi	# Store address of string to print (=param 1)
	movq $1,%rsi		# Store number of params (=param 2)
	movq $0,%rax		# No vector registers passed to printf
	call printf		# Call C library function

program_end:			# Terminate program
	movq $0,%rbx
	movq $60,%rax
	syscall

