# PURPOSE:   This program converts an input file to an output file with all
#            letters converted to uppercase.
#
# PROCESSING: 1) Open the input file
#             2) Open the output file
#             4) While we're not at the end of the input file
#               a) read part of the file into our piece of memory
#               b) go through each byte of memory
#                  if the byte is a lower-case letter, convert it to uppercase
#               c) write the piece of memory to the output file

.section .data  # We actually don't put anything in the data section in
	        # this program, but it's here for completeness
	
#######CONSTANTS########

	# System call numbers
	.equ SYS_OPEN, 2
	.equ SYS_READ, 0
	.equ SYS_WRITE, 1
	.equ SYS_CLOSE, 3
	.equ SYS_EXIT, 60

	# Options for open   (look at /usr/include/asm/fcntl.h for
	#                    various values.  You can combine them
	#                    by adding them)
	.equ O_RDONLY, 0                  # Open file options - read-only
	.equ O_CREAT_WRONLY_TRUNC, 03101  # Open file options - these options are:
	                                  # CREAT - create file if it doesn't exist
	                                  # WRONLY - we will only write to this file
	                                  # TRUNC - destroy current file contents, if any exist 

	.equ O_PERMS, 0666                # Read & Write permissions for everyone

	# End-of-file result status
	.equ END_OF_FILE, 0  # This is the return value of read() which
	                     # means we've hit the end of the file

#######BUFFERS#########

.section .bss
	# This is where the data is loaded into from
	# the data file and written from into the output file.
	# It should never exceed 16,000 for various reasons.
	.equ BUFFER_SIZE, 500
	.lcomm BUFFER_DATA, BUFFER_SIZE


#######PROGRAM CODE###

	.section .text

	# STACK POSITIONS
	.equ ST_SIZE_RESERVE, 16 # Space for local variables
	# Note: Offsets are RBP-based, which is set immediately at program start
	.equ ST_FD_IN, -16       # Local variable for input file descriptor
	.equ ST_FD_OUT, -8       # Local variable for output file descriptor
	.equ ST_ARGC, 0          # Number of arguments
	.equ ST_ARGV_0, 8        # Name of program
	.equ ST_ARGV_1, 16       # Input file name
	.equ ST_ARGV_2, 24       # Output file name

	.globl _start
_start:
	###INITIALIZE PROGRAM###
	movq %rsp, %rbp             # Create new stack frame
	subq $ST_SIZE_RESERVE, %rsp # Allocate space for our file descriptors on the stack
	###CHECK PARAMETER COUNT###
	cmpq $3, ST_ARGC(%rbp)
	je open_files
	movq $-1, %rdi              # Our return value for parameter problems
	movq $SYS_EXIT, %rax
	syscall

open_files:
open_fd_in:
	###OPEN INPUT FILE###
	movq ST_ARGV_1(%rbp), %rdi  # Input filename into %rdi
	movq $O_RDONLY, %rsi        # Read-only flag
	movq $O_PERMS, %rdx         # This doesn't really matter for reading
	movq $SYS_OPEN, %rax        # Specify "open"
	syscall 	            # Call Linux
	cmpq $0, %rax               # Check success
	jl exit                     # In case of error simply terminate

store_fd_in:
	movq  %rax, ST_FD_IN(%rbp)  # Save the returned file descriptor

open_fd_out:
	###OPEN OUTPUT FILE###
	movq ST_ARGV_2(%rbp), %rdi        # Output filename into %rdi
	movq $O_CREAT_WRONLY_TRUNC, %rsi  # Flags for writing to the file
	movq $O_PERMS, %rdx               # Permission set for new file (if it's created)
	movq $SYS_OPEN, %rax              # Open the file
	syscall                           # Call Linux
	cmpq $0, %rax                     # Check success
	jl close_input                    # In case of error close input file (already open!)

store_fd_out:
	movq %rax, ST_FD_OUT(%rbp)        # Store the file descriptor

	###BEGIN MAIN LOOP###
read_loop_begin:

	###READ IN A BLOCK FROM THE INPUT FILE###
	movq ST_FD_IN(%rbp), %rdi     # Get the input file descriptor
	movq $BUFFER_DATA, %rsi       # The location to read into
	movq $BUFFER_SIZE, %rdx       # The size of the buffer
	movq $SYS_READ, %rax
	syscall                       # Size of buffer read is returned in %eax

	###EXIT IF WE'VE REACHED THE END###
	cmpq $END_OF_FILE, %rax       # Check for end of file marker
	je end_loop                   # If found (or error), go to the end
	jl close_output               # On error just terminate

continue_read_loop:
	###CONVERT THE BLOCK TO UPPER CASE###
	movq $BUFFER_DATA, %rdi       # Location of the buffer
	movq %rax, %rsi               # Size of the buffer
	pushq $-1                     # Dummy value for stack alignment
	pushq %rax                    # Store number of bytes read for write check
	call convert_to_upper	      # Note: RAX may (will) be destroyed (caller-safe!),
	                              # but will be returned identically as return value
	###WRITE THE BLOCK OUT TO THE OUTPUT FILE###
	movq ST_FD_OUT(%rbp), %rdi    # File to use
	movq $BUFFER_DATA, %rsi       # Location of  buffer
	movq %rax, %rdx               # Size of buffer (=number of bytes actually read/converted)
	movq $SYS_WRITE, %rax
	syscall
	###CHECK WRITE SUCCESS###
	popq %rbx                     # Retrieve number of bytes read
	addq $8, %rsp                 # Remove stack alignment space
	cmpq %rax, %rbx               # Compare number read to written
	jne close_output              # If not the same, terminate program
	###CONTINUE THE LOOP###
	jmp read_loop_begin

end_loop:                         # No special error handling, so success and error
close_output:                     # are the same: we just close both files
	###CLOSE THE FILES###
	# NOTE - we don't need to do error checking on these, because 
	#        error conditions don't signify anything special here
	#        and there is nothing for us to do anyway
	movq ST_FD_OUT(%rbp), %rdi
	movq $SYS_CLOSE, %rax
	syscall
close_input:
	movq ST_FD_IN(%rbp), %rdi
	movq $SYS_CLOSE, %rax
	syscall

exit:
	###EXIT###
	movq $0, %rdi          # Standard return value for all cases
	movq $SYS_EXIT, %rax
	syscall

#####FUNCTION convert_to_upper
#
#PURPOSE:   This function actually does the conversion to upper case for a block
#
#INPUT:     The first parameter (rdi) is the location of the block of memory to convert
#           The second parameter (rsi) is the length of that buffer
#
#OUTPUT:    This function overwrites the current buffer with the upper-casified
#           version.
#           Return value: The number of bytes converted (=content of RBX), as
#                         nothing in here can happen to stop/interrupt this.
#
#VARIABLES:
#           %rax  - beginning of buffer
#           %rbx  - length of buffer (old value must be saved!)
#           %rdi  - current buffer offset
#           %r10b - current byte being examined (%r10b is the first byte of %r10)
# Note: This variable assignment is for exemplary purposes only and very suboptimal!
#

	###CONSTANTS##
	.equ  LOWERCASE_A, 'a'              # The lower boundary of our search
	.equ  LOWERCASE_Z, 'z'              # The upper boundary of our search
	.equ  UPPER_CONVERSION, 'A' - 'a'   # Conversion between upper and lower case

convert_to_upper:
	pushq %rbp                          # Prepare stack
	movq  %rsp, %rbp
	pushq %rbx                          # Save RBX

	###SET UP VARIABLES###
	movq %rdi, %rax
	movq %rsi, %rbx
	movq $0, %rdi

	# If a buffer with zero length was given us, just leave
	cmpq $0, %rbx
	je end_convert_loop

convert_loop:
	# Get the current byte
	movb (%rax,%rdi,1), %r10b

	# Go to the next byte unless it is between 'a' and 'z'
	cmpb $LOWERCASE_A, %r10b
	jl next_byte
	cmpb $LOWERCASE_Z, %r10b
	jg next_byte

	# Otherwise convert the byte to uppercase
	addb $UPPER_CONVERSION, %r10b
	# And store it back
	movb %r10b, (%rax,%rdi,1)  
next_byte:
	incq %rdi              # Next byte
	cmpq %rdi, %rbx        # Continue unless we've reached the end
	jne convert_loop

end_convert_loop:
	movq %rdi, %rax        # Store number of chars converted into RAX as return value
	popq %rbx
	movq %rbp, %rsp
	popq %rbp
	ret
