	# PURPOSE - Demonstrate the various kinds of loops in assembly language
	#           Conten: Sum up the loop index

	.section .data

	# This program has no global data

	.section .text

	.equ END,7

	.globl _start

_start:

	movq $0,%rax	# End result - initialize with 0
	# FOR-LOOP
	movq $2,%rcx	# Initialize loop counter
for_start:
	cmpq $END,%rcx	# At the end of the loop?
	jg for_end	# If not, go to end
	addq %rcx,%rax	# Add current index to result
	incq %rcx	# Increment loop counter
	jmp for_start	# Go to loop begin
for_end:

	movq $0,%rax	# End result - initialize with 0
	# REPEAT-LOOP
	movq $2,%rcx	# Initialize loop counter
repeat_start:
	addq %rcx,%rax	# Add current index to result
	incq %rcx	# Increment loop counter
	cmpq $END,%rcx	# At the end of the loop?
	jle repeat_start	# If not, go to top
repeat_end:
	# How often evaluated? Indices: 2, 3, 4, 5, 6, 7
	# Result: 27

    movq $0,%rax    # End result - initialize with 0
    # WHILE-LOOP
	movq $2,%rcx	# Initialize loop counter
while_start:
    cmpq $END,%rcx  # At the end of the loop?
    jge while_end   # If not, go to end
    addq %rcx,%rax  # Add current index to result
    incq %rcx       # Increment loop counter
    jmp while_start # Go to loop begin
while_end:
	# How often evaluated? Indices: 2, 3, 4, 5, 6
	# Result: 20

    movq $0,%rax    # End result - initialize with 0
    # LOOP
    movq $5,%rcx    # Initialize loop counter
	# Note: LOOP will always decrement, so we must start with 5 and end with 0!
loop_start:
        addq %rcx,%rax  # Add current index to result
	loop loop_start	# Decrement RCX and jump to start until it reaches zero
loop_end:
	# How often evaluated? Indices: 5, 4, 3, 2, 1
	# Result: 15

program_end:
	movq %rax,%rdi
	movq $60,%rax
	syscall

