# Preconditions
#   x5 = 6
#   x9 = 0x2004
#   M[0x2000] = 10

L6:
    lw x6, -4(x9)	# x6 = M[x9 + (-4)]
    sw x6, 8(x9) 	# M[x9 + 8] = x6
    or x4, x5, x6	# x4 = x5 OR x6
    jal x4, L6
    