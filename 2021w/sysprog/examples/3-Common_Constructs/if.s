# PURPOSE - Demonstrate IF instruction in several variants
.section .text

.globl _start

_start:
    movq %rsp,%rbp

    movq $0,%rax         # Calculate expression: Here fixed value
    cmpq $0,%rax         # Compare to 0; set flags (ZF, CF, SF, OF, PF, AF)
    je else_part         # Jump to ELSE part
    movq $1,%rdi         # Perform "A" part
    jmp continue         # Jump over ELSE part
else_part:               # Part executed if condition is false
    movq $0,%rdi         # Perform "B" part
continue:                # Continue with program

    movb $0,%al          # Set first value
    movb $1,%bl          # Set second value
    movb $255,%cl        # Set third value
    movb $55,%dl         # Set fourth value
    movq $0,%rdi         # Set initial program return value

    cmpb %al,%al         # 0==0? --> 0-0 --> ZF=1, CF=0, SF=0, OF=0 (PF=1, AF=0)
    je true1             # Will jump, as ZF == 1
l1:    
    jne false            # Will NOT jump, as ZF != 0
    jb false             # Will NOT jump, as CF != 1
    ja false             # Will NOT jump, as ZF != 0
    jl false             # Will NOT jump, as SF == OF
    jg false             # Will NOT jump, as ZF != 0

    cmpb %al,%bl         # 0==1? --> 1-0 --> ZF=0, CF=0, SF=0, OF=0 (PF=0, AF=0)
    je false             # Will NOT jump, as ZF != 1
    jne true2            # Will jump, as ZF == 0
l2:    
    jb false             # Will NOT jump, as CF != 1
    ja true3             # Will jump, as CF == 0 && ZF == 0
l3:    
    jl false             # Will NOT jump, as SF == OF
    jg true4             # Will jump, as SF == OF && ZF == 0
l4:    

    cmpb %bl,%al         # 1==0? --> 0-1 --> ZF=0, CF=1, SF=1, OF=0 (PF=1, AF=1)
    je false             # Will NOT jump, as ZF != 1
    jne true5            # Will jump, as ZF == 0
l5:    
    jb true6             # Will jump, as CF == 1
l6:    
    ja false             # Will NOT jump, as CF != 0
    jl true7             # Will jump, as SF != OF
l7:    
    jg false             # Will NOT jump, as SF != OF

    cmpb %cl,%dl         # 255/-1==55? Signed (55 - -1)= 56, Unsigned = "-200"
                         # ZF=0, CF=1, SF=0 (PF=0, OF=0, AF=1)
    je false             # Will NOT jump, as ZF != 1
    jne true8            # Will jump, as ZF == 0
l8:    
    jb true9             # Will jump, as CF == 1 (55<255)
l9:    
    ja false             # Will NOT jump, as CF != 0
    jl false             # Will NOT jump, as SF == OF
    jg true10            # Will jump, as SF == OF && ZF == 0 (55>-1)
l10:

    testq %rdx,%rdx      # 55 AND 55 --> ZF=0, SF=0, PF=0
    jz false             # Will NOT jump, as ZF != 1
    
    testb $129,%cl       # 255 AND 129 --> ZF=0, SF=1, PF=1
    js true11            # Will jump, as SF == 1
l11:    
    jmp program_end

true1:
    pushf                # incq changes the flags - so save&restore them
    incq %rdi
    popf
    jmp l1
true2:
    pushf
    incq %rdi
    popf
    jmp l2
true3:
    pushf
    incq %rdi
    popf
    jmp l3
true4:
    pushf
    incq %rdi
    popf
    jmp l4
true5:
    pushf
    incq %rdi
    popf
    jmp l5
true6:
    pushf
    incq %rdi
    popf
    jmp l6
true7:
    pushf
    incq %rdi
    popf
    jmp l7
true8:
    pushf
    incq %rdi
    popf
    jmp l8
true9:
    pushf
    incq %rdi
    popf
    jmp l9
true10:
    pushf
    incq %rdi
    popf
    jmp l10
true11:
    pushf
    incq %rdi
    popf
    jmp l11

false:
    movq $0,%rdi        # Fall through to termination

program_end:            # Terminate program
    movq %rdi,%rbx
    movq $60,%rax
    syscall
