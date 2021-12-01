   # PURPOSE:  Program to illustrate how functions work
   #           This program will compute the value of
   #           2^3 + 5^2
   #

   # Everything in the main program is stored in registers,
   # so the data section doesn't have anything.
   .section .data 

   .section .text

   .globl _start
_start:

   pushq $0                  # Stack alignment
   pushq %rax                # Preserve caller-safe registers
   pushq %rcx
   pushq %rdx
   
   movq $2,%rdi              # Store first argument
   movq $3,%rsi              # Store second argument
   call power                # Call the function

   popq %rdx                 # Restore caller-safe registers
   popq %rcx
   
   movq %rax,%r12            # Save first result into temporary register
   popq %rax                 # Restore old %rax

# -----------------------------------------------------------------------

   pushq %rax                # Preserve caller-safe registers
   pushq %rcx
   pushq %rdx
   
   movq $5,%rdi              # Store first argument
   movq $2,%rsi              # Store second argument
   call power                # Call the function

   popq %rdx                 # Restore caller-safe registers
   popq %rcx
   
   movq %rax,%rdi            # Save second result into temporary register
   popq %rax                 # Restore old %rax
                             
   addq %r12,%rdi            # The second result is in %r12
                             # Add the first one and store in %rdi

# -----------------------------------------------------------------------
   addq $8,%rsp              # Clean up stack alignment

   movq $60,%rax             # Exit (%rdi is returned)
   syscall

# -----------------------------------------------------------------------

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
   # NOTES:    The power must be 1 or greater
   #
   # VARIABLES: 
   #          %rbx - holds the base number
   #          %rcx - holds the power
   #
   #          -8(%rbp) - holds the current result
   #
   #          %rax is used for temporary storage

   .type power, @function
power:
   pushq %rbp              # Save old base pointer
   movq  %rsp,%rbp         # Make stack pointer the base pointer
   subq  $8,%rsp           # Get room for our local storage

   pushq %rbx              # Preserve callee-safe register

   movq  %rdi,%rbx         # Put first argument in %rbx
   movq  %rsi,%rcx         # Put second argument in %rcx

   movq  %rbx,-8(%rbp)     # Store current result

power_loop_start:
   cmpq  $1,%rcx           # If the power is 1, we are done
   je    end_power
   movq  -8(%rbp),%rax     # Move the current result into %rax
   imulq %rbx,%rax         # Multiply the current result by the base number
   movq  %rax,-8(%rbp)     # Store the current result 

   decq  %rcx              # Decrease the power
   jmp   power_loop_start  # Run for the next power

end_power:
   movq -8(%rbp),%rax      # Return value goes in %rax
   
   popq %rbx               # Restore callee-safe registers
   
   movq %rbp,%rsp          # Restore the stack pointer
   popq %rbp               # Restore the base pointer
   ret                     # Return to caller
