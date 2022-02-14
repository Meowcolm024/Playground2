
a.out:	file format mach-o arm64


Disassembly of section __TEXT,__text:

0000000100003f84 <_main>:
100003f84: fd 7b bf a9 	stp	x29, x30, [sp, #-16]!
100003f88: fd 03 00 91 	mov	x29, sp
100003f8c: 20 01 00 10 	adr	x0, #36
100003f90: 1f 20 03 d5 	nop
100003f94: 04 00 00 94 	bl	0x100003fa4 <_printf+0x100003fa4>
100003f98: 00 00 80 52 	mov	w0, #0
100003f9c: fd 7b c1 a8 	ldp	x29, x30, [sp], #16
100003fa0: c0 03 5f d6 	ret

Disassembly of section __TEXT,__stubs:

0000000100003fa4 <__stubs>:
100003fa4: 10 00 00 b0 	adrp	x16, 0x100004000 <__stubs+0x4>
100003fa8: 10 02 40 f9 	ldr	x16, [x16]
100003fac: 00 02 1f d6 	br	x16
