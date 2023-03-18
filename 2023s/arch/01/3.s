                    #     +0 +1 +2 +3      +0 +1 +2 +3    
li t0, 0x10000008   # BE: 10 00 00 08, LE: 08 00 00 10
lw a0, 0(t0)        # BE: D5 B7 A9 85, LE: 85 A9 B7 D5
lb a1, 5(t0)        # 0x10000008 + 5 = 0x1000000D
                    # assumption: in the given table 0x1000001C is replaced with 
                    # 0x1000000C because otherwise we would read unknown memory and
                    # this seems unintentional
                    # BE: 00 00 00 3D, LE: 3D 00 00 00
slli a0, a0, 8      # standard riscv is little-endian so that's what the shift is 
                    # working on
                    # BE: 00 00 00 00, LE: 00 00 00 00
xor a1, a1, a0      # see above on operation endianness
                    # BE: D5 B7 A9 B8, LE: B8 A9 B7 D5