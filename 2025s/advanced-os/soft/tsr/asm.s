_start:
pushq %rbx			    # Save register we are using for indirect calls
call _begin				# Call to next instruction (relative offset 0); useless, but puts our current RIP onto the stack!
_begin:
popq %rbx			    # Retrieve our own address and restore the stack
#leaq (%rip),%rbx		# Alternative to the two instructions before; must adjust subtraction below from 6 to 8 then too!
# Save registers
pushf				    # Save flags
# Calculate base address
subq $6,%rbx			# Subtract length of (push+call) instructions to get at start address of program
# subq $8,%rbx			# Subtract length of (push+leaq) instructions to get at start address of program
# Check if we should print the message
# Signature: static bool (*filterProc)(struct input_handle *handle, unsigned int type, unsigned int code, int value)=NULL;
# RDI = handle; we don't care about this one
cmpq $1,%rsi			# Compare RSI (=type) to EV_KEY (=1) 
jne _end				# If not matching, skip printing; relative jump (32 bytes forward) -> no base address problem
cmpq $35,%rdx		    # Compare RDX (=code) to "h" (=35) 
jne _end				# If not matching, skip printing
cmpq $0,%rcx			# Compare RCX (=value) to key-up (=0) 
jne _end				# If not matching, skip printing
# Call printk with string
pushq %rdi			    # Save register - we are overwriting it for the printk call
pushq %rbx			    # Save our own base address (needed for retrieving handler address)
leaq 2000(%rbx),%rdi	# Load address of string. NOTE: offset is hardcoded!
leaq 4000(%rbx),%rbx	# Load address of printk. NOTE: address of "relocation table" and "index" in it is hardcoded
call *(%rbx)			# Call printk. Must be an indirect call as we don't know where we are (-> no relative call) and could be more than 32 bits (-> absolute call)
# Restore register
popq %rbx			    # Restore base address
popq %rdi			    # Restore register we clobbered
_end:
# Call original handler
leaq 4008(%rbx),%rbx	# Load address of old handler. NOTE: "index" in "relocation table" is 1
popf					# Restore flags
call *(%rbx)			# Call old handler
# Restore everything and return (don't touch RAX: return value from old handler is our "own" return value!)
popq %rbx			    # Restore register we used for indirect calls
ret					    # Return from callback
