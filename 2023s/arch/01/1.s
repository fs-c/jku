.data

.globl main

.text
main:

a:
	# beim left shift ist nichts besonderes zu beachten/beobachten.
    # beim right shift wurde ein arithmetic right shift verwendet weil
    # integer signed ist. hier wird das MSB über alle "leeren" positionen
    # kopiert (sign extension).

	lui a0, 0xE			# a0 = 0xE000, 11th bit of 0xDD44 is set so increase by one
    addi a0, a0, 0xDD4	# a0 = 0xDD44
    
    lui a1, 0x10		# a1 = 0x10000, see above
    addi a1, a1, 0xFFF	# a1 = 0xFFFF
    
    # (((((a0 / 0xEE) + 0xD) << 0x4) << 20) >> 0x14) & a1
    addi t0, zero, 0xEE	# temp var for division
    div a0, a0, t0		# a0 /= 0xEE
    addi a0, a0, 0xD	# a0 += 0xD
    slli a0, a0, 0x4	# a0 <<= 0x4
    slli a0, a0, 20		# a0 <<= 20
    srai a0, a0, 0x14	# a0 >>= 0x14
    and a0, a0, a1		# a0 &= a1
    
b:
	# long long ist immer ein 64-bit integer, long ist entweder 32- oder 64-bit
    # abhängig von der architektur (RV32 oder RV64), unterscheiden sich also nur 
    # für RV32. void foo(long long param) unter RV32 bekommt param in a0 und a1, 
    # unter RV64 in a0.
    
c:
	lui a0, 0x30400		# a0 = 0x30400000, +1 again because 11th bit is set
    addi a0, a0, 0xB80	# a0 = 0x303FFB80
    addi t0, zero, 0	# loop counter
    addi t1, zero, 6	# max iterations
loop:
	srai a0, a0, 1		# a0 >>= 1
    addi t0, t0, 1		# i++
    blt t0, t1, loop	# continue loop if counter < 6
end:
    