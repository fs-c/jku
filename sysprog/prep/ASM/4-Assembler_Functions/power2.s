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
   movq $2,%rdi              # Store first argument
   movq $3,%rsi              # Store second argument
   call  power               # Call the function
   movq  %rax,%r11           # Save first result into temporary register
# -----------------------------------------------------------------------
   movq $5,%rdi              # Store first argument
   movq $2,%rsi              # Store second argument
   call  power               # Call the function
   movq  %rax,%rdi           # Save second result into reg for exit value
   addq  %r11,%rdi           # Add the first result to it
# -----------------------------------------------------------------------
   movq  $60,%rax            # Exit (%rdi is returned)
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
   # NOTES:    The power must be 0 or greater
   #           We do not use the stack here at all, so we skip 
   #           both prologue and epilogue!
   #
   # VARIABLES: 
   #          %rdi - holds the base number
   #          %rsi - holds the power
   #          %rax is used for temporary storage

   .type power, @function
power:
   movq  $1,%rax
   cmpq  $0,%rsi           # If the power is 0, we return 1
   je    end_power
   movq  %rdi,%rax         # Prepare local variable for first round
power_loop_start:
   cmpq  $1,%rsi           # If the power is 1, we are done
   je    end_power
   imulq %rdi,%rax         # Multiply the current result by the base number
   decq  %rsi              # Decrease the power
   jmp   power_loop_start  # Run for the next power
end_power:
   ret                     # Return to caller
