
a.out:     file format elf64-x86-64


Disassembly of section .init:

0000000000401000 <_init>:
  401000:	48 83 ec 08          	sub    rsp,0x8
  401004:	48 8b 05 ed 2f 00 00 	mov    rax,QWORD PTR [rip+0x2fed]        # 403ff8 <__gmon_start__>
  40100b:	48 85 c0             	test   rax,rax
  40100e:	74 02                	je     401012 <_init+0x12>
  401010:	ff d0                	call   rax
  401012:	48 83 c4 08          	add    rsp,0x8
  401016:	c3                   	ret    

Disassembly of section .plt:

0000000000401020 <.plt>:
  401020:	ff 35 e2 2f 00 00    	push   QWORD PTR [rip+0x2fe2]        # 404008 <_GLOBAL_OFFSET_TABLE_+0x8>
  401026:	ff 25 e4 2f 00 00    	jmp    QWORD PTR [rip+0x2fe4]        # 404010 <_GLOBAL_OFFSET_TABLE_+0x10>
  40102c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

0000000000401030 <_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@plt>:
  401030:	ff 25 e2 2f 00 00    	jmp    QWORD PTR [rip+0x2fe2]        # 404018 <_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@GLIBCXX_3.4>
  401036:	68 00 00 00 00       	push   0x0
  40103b:	e9 e0 ff ff ff       	jmp    401020 <.plt>

0000000000401040 <__cxa_atexit@plt>:
  401040:	ff 25 da 2f 00 00    	jmp    QWORD PTR [rip+0x2fda]        # 404020 <__cxa_atexit@GLIBC_2.2.5>
  401046:	68 01 00 00 00       	push   0x1
  40104b:	e9 d0 ff ff ff       	jmp    401020 <.plt>

0000000000401050 <_ZNSolsEPFRSoS_E@plt>:
  401050:	ff 25 d2 2f 00 00    	jmp    QWORD PTR [rip+0x2fd2]        # 404028 <_ZNSolsEPFRSoS_E@GLIBCXX_3.4>
  401056:	68 02 00 00 00       	push   0x2
  40105b:	e9 c0 ff ff ff       	jmp    401020 <.plt>

0000000000401060 <_ZNSt8ios_base4InitC1Ev@plt>:
  401060:	ff 25 ca 2f 00 00    	jmp    QWORD PTR [rip+0x2fca]        # 404030 <_ZNSt8ios_base4InitC1Ev@GLIBCXX_3.4>
  401066:	68 03 00 00 00       	push   0x3
  40106b:	e9 b0 ff ff ff       	jmp    401020 <.plt>

0000000000401070 <_ZNSolsEi@plt>:
  401070:	ff 25 c2 2f 00 00    	jmp    QWORD PTR [rip+0x2fc2]        # 404038 <_ZNSolsEi@GLIBCXX_3.4>
  401076:	68 04 00 00 00       	push   0x4
  40107b:	e9 a0 ff ff ff       	jmp    401020 <.plt>

0000000000401080 <_ZNSt8ios_base4InitD1Ev@plt>:
  401080:	ff 25 ba 2f 00 00    	jmp    QWORD PTR [rip+0x2fba]        # 404040 <_ZNSt8ios_base4InitD1Ev@GLIBCXX_3.4>
  401086:	68 05 00 00 00       	push   0x5
  40108b:	e9 90 ff ff ff       	jmp    401020 <.plt>

Disassembly of section .text:

0000000000401090 <__cxx_global_var_init>:
  401090:	55                   	push   rbp
  401091:	48 89 e5             	mov    rbp,rsp
  401094:	48 83 ec 10          	sub    rsp,0x10
  401098:	48 bf 71 41 40 00 00 	movabs rdi,0x404171
  40109f:	00 00 00 
  4010a2:	e8 b9 ff ff ff       	call   401060 <_ZNSt8ios_base4InitC1Ev@plt>
  4010a7:	48 bf 80 10 40 00 00 	movabs rdi,0x401080
  4010ae:	00 00 00 
  4010b1:	48 be 71 41 40 00 00 	movabs rsi,0x404171
  4010b8:	00 00 00 
  4010bb:	48 ba 50 40 40 00 00 	movabs rdx,0x404050
  4010c2:	00 00 00 
  4010c5:	e8 76 ff ff ff       	call   401040 <__cxa_atexit@plt>
  4010ca:	89 45 fc             	mov    DWORD PTR [rbp-0x4],eax
  4010cd:	48 83 c4 10          	add    rsp,0x10
  4010d1:	5d                   	pop    rbp
  4010d2:	c3                   	ret    
  4010d3:	66 2e 0f 1f 84 00 00 	nop    WORD PTR cs:[rax+rax*1+0x0]
  4010da:	00 00 00 
  4010dd:	0f 1f 00             	nop    DWORD PTR [rax]

00000000004010e0 <_GLOBAL__sub_I_a.cpp>:
  4010e0:	55                   	push   rbp
  4010e1:	48 89 e5             	mov    rbp,rsp
  4010e4:	e8 a7 ff ff ff       	call   401090 <__cxx_global_var_init>
  4010e9:	5d                   	pop    rbp
  4010ea:	c3                   	ret    
  4010eb:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]

00000000004010f0 <_start>:
  4010f0:	31 ed                	xor    ebp,ebp
  4010f2:	49 89 d1             	mov    r9,rdx
  4010f5:	5e                   	pop    rsi
  4010f6:	48 89 e2             	mov    rdx,rsp
  4010f9:	48 83 e4 f0          	and    rsp,0xfffffffffffffff0
  4010fd:	50                   	push   rax
  4010fe:	54                   	push   rsp
  4010ff:	49 c7 c0 90 12 40 00 	mov    r8,0x401290
  401106:	48 c7 c1 30 12 40 00 	mov    rcx,0x401230
  40110d:	48 c7 c7 e0 11 40 00 	mov    rdi,0x4011e0
  401114:	ff 15 d6 2e 00 00    	call   QWORD PTR [rip+0x2ed6]        # 403ff0 <__libc_start_main@GLIBC_2.2.5>
  40111a:	f4                   	hlt    
  40111b:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]

0000000000401120 <_dl_relocate_static_pie>:
  401120:	c3                   	ret    
  401121:	66 2e 0f 1f 84 00 00 	nop    WORD PTR cs:[rax+rax*1+0x0]
  401128:	00 00 00 
  40112b:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]

0000000000401130 <deregister_tm_clones>:
  401130:	b8 58 40 40 00       	mov    eax,0x404058
  401135:	48 3d 58 40 40 00    	cmp    rax,0x404058
  40113b:	74 13                	je     401150 <deregister_tm_clones+0x20>
  40113d:	b8 00 00 00 00       	mov    eax,0x0
  401142:	48 85 c0             	test   rax,rax
  401145:	74 09                	je     401150 <deregister_tm_clones+0x20>
  401147:	bf 58 40 40 00       	mov    edi,0x404058
  40114c:	ff e0                	jmp    rax
  40114e:	66 90                	xchg   ax,ax
  401150:	c3                   	ret    
  401151:	66 66 2e 0f 1f 84 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
  401158:	00 00 00 00 
  40115c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

0000000000401160 <register_tm_clones>:
  401160:	be 58 40 40 00       	mov    esi,0x404058
  401165:	48 81 ee 58 40 40 00 	sub    rsi,0x404058
  40116c:	48 c1 fe 03          	sar    rsi,0x3
  401170:	48 89 f0             	mov    rax,rsi
  401173:	48 c1 e8 3f          	shr    rax,0x3f
  401177:	48 01 c6             	add    rsi,rax
  40117a:	48 d1 fe             	sar    rsi,1
  40117d:	74 11                	je     401190 <register_tm_clones+0x30>
  40117f:	b8 00 00 00 00       	mov    eax,0x0
  401184:	48 85 c0             	test   rax,rax
  401187:	74 07                	je     401190 <register_tm_clones+0x30>
  401189:	bf 58 40 40 00       	mov    edi,0x404058
  40118e:	ff e0                	jmp    rax
  401190:	c3                   	ret    
  401191:	66 66 2e 0f 1f 84 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
  401198:	00 00 00 00 
  40119c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

00000000004011a0 <__do_global_dtors_aux>:
  4011a0:	80 3d c9 2f 00 00 00 	cmp    BYTE PTR [rip+0x2fc9],0x0        # 404170 <completed.7325>
  4011a7:	75 17                	jne    4011c0 <__do_global_dtors_aux+0x20>
  4011a9:	55                   	push   rbp
  4011aa:	48 89 e5             	mov    rbp,rsp
  4011ad:	e8 7e ff ff ff       	call   401130 <deregister_tm_clones>
  4011b2:	c6 05 b7 2f 00 00 01 	mov    BYTE PTR [rip+0x2fb7],0x1        # 404170 <completed.7325>
  4011b9:	5d                   	pop    rbp
  4011ba:	c3                   	ret    
  4011bb:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]
  4011c0:	c3                   	ret    
  4011c1:	66 66 2e 0f 1f 84 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
  4011c8:	00 00 00 00 
  4011cc:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

00000000004011d0 <frame_dummy>:
  4011d0:	eb 8e                	jmp    401160 <register_tm_clones>
  4011d2:	66 2e 0f 1f 84 00 00 	nop    WORD PTR cs:[rax+rax*1+0x0]
  4011d9:	00 00 00 
  4011dc:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

00000000004011e0 <main>:
  4011e0:	55                   	push   rbp
  4011e1:	48 89 e5             	mov    rbp,rsp
  4011e4:	48 83 ec 10          	sub    rsp,0x10
  4011e8:	c7 45 fc 00 00 00 00 	mov    DWORD PTR [rbp-0x4],0x0
  4011ef:	c7 45 f8 ea 00 00 00 	mov    DWORD PTR [rbp-0x8],0xea
  4011f6:	8b 75 f8             	mov    esi,DWORD PTR [rbp-0x8]
  4011f9:	48 bf 60 40 40 00 00 	movabs rdi,0x404060
  401200:	00 00 00 
  401203:	e8 68 fe ff ff       	call   401070 <_ZNSolsEi@plt>
  401208:	48 89 c7             	mov    rdi,rax
  40120b:	48 be 30 10 40 00 00 	movabs rsi,0x401030
  401212:	00 00 00 
  401215:	e8 36 fe ff ff       	call   401050 <_ZNSolsEPFRSoS_E@plt>
  40121a:	31 c9                	xor    ecx,ecx
  40121c:	48 89 45 f0          	mov    QWORD PTR [rbp-0x10],rax
  401220:	89 c8                	mov    eax,ecx
  401222:	48 83 c4 10          	add    rsp,0x10
  401226:	5d                   	pop    rbp
  401227:	c3                   	ret    
  401228:	0f 1f 84 00 00 00 00 	nop    DWORD PTR [rax+rax*1+0x0]
  40122f:	00 

0000000000401230 <__libc_csu_init>:
  401230:	41 57                	push   r15
  401232:	49 89 d7             	mov    r15,rdx
  401235:	41 56                	push   r14
  401237:	49 89 f6             	mov    r14,rsi
  40123a:	41 55                	push   r13
  40123c:	41 89 fd             	mov    r13d,edi
  40123f:	41 54                	push   r12
  401241:	4c 8d 25 80 2b 00 00 	lea    r12,[rip+0x2b80]        # 403dc8 <__frame_dummy_init_array_entry>
  401248:	55                   	push   rbp
  401249:	48 8d 2d 88 2b 00 00 	lea    rbp,[rip+0x2b88]        # 403dd8 <__init_array_end>
  401250:	53                   	push   rbx
  401251:	4c 29 e5             	sub    rbp,r12
  401254:	48 83 ec 08          	sub    rsp,0x8
  401258:	e8 a3 fd ff ff       	call   401000 <_init>
  40125d:	48 c1 fd 03          	sar    rbp,0x3
  401261:	74 1b                	je     40127e <__libc_csu_init+0x4e>
  401263:	31 db                	xor    ebx,ebx
  401265:	0f 1f 00             	nop    DWORD PTR [rax]
  401268:	4c 89 fa             	mov    rdx,r15
  40126b:	4c 89 f6             	mov    rsi,r14
  40126e:	44 89 ef             	mov    edi,r13d
  401271:	41 ff 14 dc          	call   QWORD PTR [r12+rbx*8]
  401275:	48 83 c3 01          	add    rbx,0x1
  401279:	48 39 dd             	cmp    rbp,rbx
  40127c:	75 ea                	jne    401268 <__libc_csu_init+0x38>
  40127e:	48 83 c4 08          	add    rsp,0x8
  401282:	5b                   	pop    rbx
  401283:	5d                   	pop    rbp
  401284:	41 5c                	pop    r12
  401286:	41 5d                	pop    r13
  401288:	41 5e                	pop    r14
  40128a:	41 5f                	pop    r15
  40128c:	c3                   	ret    
  40128d:	0f 1f 00             	nop    DWORD PTR [rax]

0000000000401290 <__libc_csu_fini>:
  401290:	c3                   	ret    

Disassembly of section .fini:

0000000000401294 <_fini>:
  401294:	48 83 ec 08          	sub    rsp,0x8
  401298:	48 83 c4 08          	add    rsp,0x8
  40129c:	c3                   	ret    
