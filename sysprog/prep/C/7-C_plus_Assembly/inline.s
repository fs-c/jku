	.file	"inline.c"
# GNU C (GCC) version 4.8.5 20150623 (Red Hat 4.8.5-36) (x86_64-redhat-linux)
#	compiled by GNU C version 4.8.5 20150623 (Red Hat 4.8.5-36), GMP version 6.0.0, MPFR version 3.1.1, MPC version 1.0.1
# GGC heuristics: --param ggc-min-expand=100 --param ggc-min-heapsize=131072
# options passed:  inline.c -mtune=generic -march=x86-64 -g -Wall
# -Wpedantic -ansi -fverbose-asm
# options enabled:  -faggressive-loop-optimizations
# -fasynchronous-unwind-tables -fauto-inc-dec -fbranch-count-reg -fcommon
# -fdelete-null-pointer-checks -fdwarf2-cfi-asm -fearly-inlining
# -feliminate-unused-debug-types -ffunction-cse -fgcse-lm -fgnu-runtime
# -fgnu-unique -fident -finline-atomics -fira-hoist-pressure
# -fira-share-save-slots -fira-share-spill-slots -fivopts
# -fkeep-static-consts -fleading-underscore -fmath-errno
# -fmerge-debug-strings -fmove-loop-invariants -fpeephole
# -fprefetch-loop-arrays -freg-struct-return
# -fsched-critical-path-heuristic -fsched-dep-count-heuristic
# -fsched-group-heuristic -fsched-interblock -fsched-last-insn-heuristic
# -fsched-rank-heuristic -fsched-spec -fsched-spec-insn-heuristic
# -fsched-stalled-insns-dep -fshow-column -fsigned-zeros
# -fsplit-ivs-in-unroller -fstrict-volatile-bitfields -fsync-libcalls
# -ftrapping-math -ftree-coalesce-vars -ftree-cselim -ftree-forwprop
# -ftree-loop-if-convert -ftree-loop-im -ftree-loop-ivcanon
# -ftree-loop-optimize -ftree-parallelize-loops= -ftree-phiprop -ftree-pta
# -ftree-reassoc -ftree-scev-cprop -ftree-slp-vectorize
# -ftree-vect-loop-version -funit-at-a-time -funwind-tables -fverbose-asm
# -fzero-initialized-in-bss -m128bit-long-double -m64 -m80387
# -maccumulate-outgoing-args -malign-stringops -mfancy-math-387
# -mfp-ret-in-387 -mfxsr -mglibc -mieee-fp -mlong-double-80 -mmmx -mno-sse4
# -mpush-args -mred-zone -msse -msse2 -mtls-direct-seg-refs

	.text
.Ltext0:
	.type	cpuid, @function
cpuid:
.LFB0:
	.file 1 "inline.c"
	.loc 1 7 0
	.cfi_startproc
	pushq	%rbp	#
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp	#,
	.cfi_def_cfa_register 6
	pushq	%rbx	#
	.cfi_offset 3, -24
	movl	%edi, -12(%rbp)	# code, code
	movq	%rsi, -24(%rbp)	# a, a
	movq	%rdx, -32(%rbp)	# b, b
	movq	%rcx, -40(%rbp)	# d, d
	.loc 1 8 0
	movl	-12(%rbp), %eax	# code, tmp62
#APP
# 8 "inline.c" 1
	cpuid

# 0 "" 2
#NO_APP
	movl	%ebx, %esi	# tmp60, tmp60
	movq	-24(%rbp), %rcx	# a, tmp63
	movl	%eax, (%rcx)	# tmp59, *a_1(D)
	movq	-32(%rbp), %rax	# b, tmp64
	movl	%esi, (%rax)	# tmp60, *b_2(D)
	movq	-40(%rbp), %rax	# d, tmp65
	movl	%edx, (%rax)	# tmp61, *d_3(D)
	.loc 1 9 0
	popq	%rbx	#
	popq	%rbp	#
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	cpuid, .-cpuid
	.globl	clearArray
	.type	clearArray, @function
clearArray:
.LFB1:
	.loc 1 11 0
	.cfi_startproc
	pushq	%rbp	#
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp	#,
	.cfi_def_cfa_register 6
	movq	%rdi, -8(%rbp)	# ptr, ptr
	movq	%rsi, -16(%rbp)	# length, length
	.loc 1 12 0
	movq	-8(%rbp), %rdx	# ptr, tmp60
	movq	-16(%rbp), %rax	# length, tmp61
#APP
# 12 "inline.c" 1
	cmpq $0,%rax	# length
jle end
start:
decq %rax	# length
movl $0,(%rdx,%rax,4)	# tmp60, length
cmpq $0,%rax	# length
jg start
end:

# 0 "" 2
#NO_APP
	movq	%rax, -16(%rbp)	# length, length
	.loc 1 25 0
	popq	%rbp	#
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	clearArray, .-clearArray
	.section	.rodata
	.align 8
.LC0:
	.string	"CPUID: A=%0X, B=%0X, D=%0X\n%c%c%c%c %c%c%c%c\n\n"
.LC1:
	.string	"%d"
.LC2:
	.string	", "
.LC3:
	.string	"Array successfully cleared!"
.LC4:
	.string	"ERROR: Array NOT cleared!"
	.text
	.globl	main
	.type	main, @function
main:
.LFB2:
	.loc 1 27 0
	.cfi_startproc
	pushq	%rbp	#
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp	#,
	.cfi_def_cfa_register 6
	pushq	%r12	#
	pushq	%rbx	#
	subq	$80, %rsp	#,
	.cfi_offset 12, -24
	.cfi_offset 3, -32
	.loc 1 33 0
	leaq	-44(%rbp), %rcx	#, tmp98
	leaq	-40(%rbp), %rdx	#, tmp99
	leaq	-36(%rbp), %rax	#, tmp100
	movq	%rax, %rsi	# tmp100,
	movl	$0, %edi	#,
	call	cpuid	#
	.loc 1 35 0
	movl	-44(%rbp), %eax	# d, d.0
	shrl	$24, %eax	#, D.1862
	movl	%eax, %r12d	# D.1862, D.1862
	movl	-44(%rbp), %eax	# d, d.1
	shrl	$16, %eax	#, D.1862
	movzbl	%al, %r9d	# D.1862, D.1862
	movl	-44(%rbp), %eax	# d, d.2
	shrl	$8, %eax	#, D.1862
	movzbl	%al, %r8d	# D.1862, D.1862
	movl	-44(%rbp), %eax	# d, d.3
	movzbl	%al, %edi	# d.3, D.1862
	movl	-40(%rbp), %eax	# b, b.4
	shrl	$24, %eax	#, D.1862
	movl	%eax, %ebx	# D.1862, D.1862
	movl	-40(%rbp), %eax	# b, b.5
	shrl	$16, %eax	#, D.1862
	movzbl	%al, %esi	# D.1862, D.1862
	movl	-40(%rbp), %eax	# b, b.6
	shrl	$8, %eax	#, D.1862
	movzbl	%al, %r11d	# D.1862, D.1862
	movl	-40(%rbp), %eax	# b, b.7
	movzbl	%al, %r10d	# b.7, D.1862
	movl	-44(%rbp), %ecx	# d, d.8
	movl	-40(%rbp), %edx	# b, b.9
	movl	-36(%rbp), %eax	# a, a.10
	movl	%r12d, 40(%rsp)	# D.1862,
	movl	%r9d, 32(%rsp)	# D.1862,
	movl	%r8d, 24(%rsp)	# D.1862,
	movl	%edi, 16(%rsp)	# D.1862,
	movl	%ebx, 8(%rsp)	# D.1862,
	movl	%esi, (%rsp)	# D.1862,
	movl	%r11d, %r9d	# D.1862,
	movl	%r10d, %r8d	# D.1862,
	movl	%eax, %esi	# a.10,
	movl	$.LC0, %edi	#,
	movl	$0, %eax	#,
	call	printf	#
	.loc 1 38 0
	movl	$40, %edi	#,
	call	malloc	#
	movq	%rax, -32(%rbp)	# tmp101, ptr
	.loc 1 41 0
	movl	$0, -20(%rbp)	#, i
	jmp	.L4	#
.L5:
	.loc 1 42 0 discriminator 2
	movl	-20(%rbp), %eax	# i, D.1863
	leaq	0(,%rax,4), %rdx	#, D.1863
	movq	-32(%rbp), %rax	# ptr, tmp102
	addq	%rax, %rdx	# tmp102, D.1864
	movl	-20(%rbp), %eax	# i, tmp103
	subl	$4, %eax	#, D.1862
	movl	%eax, (%rdx)	# D.1865, *_32
	.loc 1 41 0 discriminator 2
	addl	$1, -20(%rbp)	#, i
.L4:
	.loc 1 41 0 is_stmt 0 discriminator 1
	cmpl	$9, -20(%rbp)	#, i
	jbe	.L5	#,
	.loc 1 46 0 is_stmt 1
	movq	-32(%rbp), %rax	# ptr, tmp104
	movl	$10, %esi	#,
	movq	%rax, %rdi	# tmp104,
	call	clearArray	#
	.loc 1 49 0
	movl	$1, -24(%rbp)	#, check
	.loc 1 50 0
	movl	$0, -20(%rbp)	#, i
	jmp	.L6	#
.L10:
	.loc 1 51 0
	movl	-20(%rbp), %eax	# i, D.1863
	leaq	0(,%rax,4), %rdx	#, D.1863
	movq	-32(%rbp), %rax	# ptr, tmp105
	addq	%rdx, %rax	# D.1863, D.1864
	movl	(%rax), %eax	# *_40, D.1865
	movl	%eax, %esi	# D.1865,
	movl	$.LC1, %edi	#,
	movl	$0, %eax	#,
	call	printf	#
	.loc 1 52 0
	cmpl	$8, -20(%rbp)	#, i
	ja	.L7	#,
	.loc 1 53 0
	movl	$.LC2, %edi	#,
	movl	$0, %eax	#,
	call	printf	#
.L7:
	.loc 1 55 0
	cmpl	$0, -24(%rbp)	#, check
	je	.L8	#,
	.loc 1 55 0 is_stmt 0 discriminator 1
	movl	-20(%rbp), %eax	# i, D.1863
	leaq	0(,%rax,4), %rdx	#, D.1863
	movq	-32(%rbp), %rax	# ptr, tmp106
	addq	%rdx, %rax	# D.1863, D.1864
	movl	(%rax), %eax	# *_44, D.1865
	testl	%eax, %eax	# D.1865
	jne	.L8	#,
	.loc 1 55 0 discriminator 3
	movl	$1, %eax	#, iftmp.11
	jmp	.L9	#
.L8:
	.loc 1 55 0 discriminator 2
	movl	$0, %eax	#, iftmp.11
.L9:
	.loc 1 55 0 discriminator 4
	movl	%eax, -24(%rbp)	# iftmp.11, check
	.loc 1 50 0 is_stmt 1 discriminator 4
	addl	$1, -20(%rbp)	#, i
.L6:
	.loc 1 50 0 is_stmt 0 discriminator 1
	cmpl	$9, -20(%rbp)	#, i
	jbe	.L10	#,
	.loc 1 57 0 is_stmt 1
	movl	$10, %edi	#,
	call	putchar	#
	.loc 1 58 0
	cmpl	$0, -24(%rbp)	#, check
	je	.L11	#,
	.loc 1 59 0
	movl	$.LC3, %edi	#,
	call	puts	#
	jmp	.L12	#
.L11:
	.loc 1 61 0
	movl	$.LC4, %edi	#,
	call	puts	#
.L12:
	.loc 1 65 0
	movq	-32(%rbp), %rax	# ptr, tmp107
	movq	%rax, %rdi	# tmp107,
	call	free	#
	.loc 1 67 0
	movl	$0, %eax	#, D.1865
	.loc 1 68 0
	addq	$80, %rsp	#,
	popq	%rbx	#
	popq	%r12	#
	popq	%rbp	#
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE2:
	.size	main, .-main
.Letext0:
	.file 2 "/usr/include/stdint.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x191
	.value	0x4
	.long	.Ldebug_abbrev0
	.byte	0x8
	.uleb128 0x1
	.long	.LASF17
	.byte	0x1
	.long	.LASF18
	.long	.LASF19
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x2
	.byte	0x8
	.byte	0x7
	.long	.LASF0
	.uleb128 0x2
	.byte	0x1
	.byte	0x8
	.long	.LASF1
	.uleb128 0x2
	.byte	0x2
	.byte	0x7
	.long	.LASF2
	.uleb128 0x2
	.byte	0x4
	.byte	0x7
	.long	.LASF3
	.uleb128 0x2
	.byte	0x1
	.byte	0x6
	.long	.LASF4
	.uleb128 0x2
	.byte	0x2
	.byte	0x5
	.long	.LASF5
	.uleb128 0x3
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x2
	.byte	0x8
	.byte	0x5
	.long	.LASF6
	.uleb128 0x2
	.byte	0x8
	.byte	0x7
	.long	.LASF7
	.uleb128 0x2
	.byte	0x1
	.byte	0x6
	.long	.LASF8
	.uleb128 0x4
	.long	.LASF9
	.byte	0x2
	.byte	0x26
	.long	0x57
	.uleb128 0x4
	.long	.LASF10
	.byte	0x2
	.byte	0x33
	.long	0x42
	.uleb128 0x4
	.long	.LASF11
	.byte	0x2
	.byte	0x37
	.long	0x2d
	.uleb128 0x5
	.long	.LASF20
	.byte	0x1
	.byte	0x7
	.quad	.LFB0
	.quad	.LFE0-.LFB0
	.uleb128 0x1
	.byte	0x9c
	.long	0xe4
	.uleb128 0x6
	.long	.LASF12
	.byte	0x1
	.byte	0x7
	.long	0x7e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.uleb128 0x7
	.string	"a"
	.byte	0x1
	.byte	0x7
	.long	0xe4
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x7
	.string	"b"
	.byte	0x1
	.byte	0x7
	.long	0xe4
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x7
	.string	"d"
	.byte	0x1
	.byte	0x7
	.long	0xe4
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.byte	0
	.uleb128 0x8
	.byte	0x8
	.long	0x7e
	.uleb128 0x9
	.long	.LASF14
	.byte	0x1
	.byte	0xb
	.quad	.LFB1
	.quad	.LFE1-.LFB1
	.uleb128 0x1
	.byte	0x9c
	.long	0x124
	.uleb128 0x7
	.string	"ptr"
	.byte	0x1
	.byte	0xb
	.long	0x124
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x6
	.long	.LASF13
	.byte	0x1
	.byte	0xb
	.long	0x89
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.byte	0
	.uleb128 0x8
	.byte	0x8
	.long	0x73
	.uleb128 0xa
	.long	.LASF15
	.byte	0x1
	.byte	0x1b
	.long	0x57
	.quad	.LFB2
	.quad	.LFE2-.LFB2
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0xb
	.string	"ptr"
	.byte	0x1
	.byte	0x1c
	.long	0x124
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0xb
	.string	"i"
	.byte	0x1
	.byte	0x1d
	.long	0x42
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0xc
	.long	.LASF16
	.byte	0x1
	.byte	0x1e
	.long	0x42
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0xb
	.string	"a"
	.byte	0x1
	.byte	0x20
	.long	0x7e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0xb
	.string	"b"
	.byte	0x1
	.byte	0x20
	.long	0x7e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0xb
	.string	"d"
	.byte	0x1
	.byte	0x20
	.long	0x7e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -60
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0x11
	.byte	0x1
	.uleb128 0x25
	.uleb128 0xe
	.uleb128 0x13
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1b
	.uleb128 0xe
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x8
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x2117
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x2117
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x2116
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	0
	.quad	0
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF2:
	.string	"short unsigned int"
.LASF3:
	.string	"unsigned int"
.LASF16:
	.string	"check"
.LASF18:
	.string	"inline.c"
.LASF13:
	.string	"length"
.LASF4:
	.string	"signed char"
.LASF0:
	.string	"long unsigned int"
.LASF20:
	.string	"cpuid"
.LASF11:
	.string	"uint64_t"
.LASF8:
	.string	"char"
.LASF1:
	.string	"unsigned char"
.LASF15:
	.string	"main"
.LASF10:
	.string	"uint32_t"
.LASF6:
	.string	"long int"
.LASF17:
	.string	"GNU C 4.8.5 20150623 (Red Hat 4.8.5-36) -mtune=generic -march=x86-64 -g -ansi"
.LASF12:
	.string	"code"
.LASF19:
	.string	"/mnt/13. C plus Assembly - Source"
.LASF14:
	.string	"clearArray"
.LASF5:
	.string	"short int"
.LASF9:
	.string	"int32_t"
.LASF7:
	.string	"sizetype"
	.ident	"GCC: (GNU) 4.8.5 20150623 (Red Hat 4.8.5-36)"
	.section	.note.GNU-stack,"",@progbits
