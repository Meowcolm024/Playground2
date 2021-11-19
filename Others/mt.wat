	.text
	.file	"mt.989b00c1-cgu.0"
	.section	.text._ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E,"",@
	.functype	_ZN3std2rt19lang_start_internal17h0a36e5f1c84a3c30E (i32, i32, i32, i32) -> (i32)
	.functype	_ZN3std3sys4wasm7process8ExitCode6as_i3217h695c859b57e9a521E (i32) -> (i32)
	.functype	_ZN4core9panicking5panic17hb05521048dcb55f3E (i32, i32, i32) -> ()
	.type	_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E,@function
_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E:
	.functype	_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E (i32) -> ()
	local.get	0
	call	_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E
	call	_ZN4core4hint9black_box17h77f9490a0e4cf303E
	return
	end_function
.Lfunc_end0:
	.size	_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E, .Lfunc_end0-_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E

	.section	.text._ZN3std2rt10lang_start17hf2384963b248006fE,"",@
	.hidden	_ZN3std2rt10lang_start17hf2384963b248006fE
	.globl	_ZN3std2rt10lang_start17hf2384963b248006fE
	.type	_ZN3std2rt10lang_start17hf2384963b248006fE,@function
_ZN3std2rt10lang_start17hf2384963b248006fE:
	.functype	_ZN3std2rt10lang_start17hf2384963b248006fE (i32, i32, i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	3
	i32.const	16
	local.set	4
	local.get	3
	local.get	4
	i32.sub 
	local.set	5
	local.get	5
	global.set	__stack_pointer
	local.get	5
	local.get	0
	i32.store	12
	i32.const	12
	local.set	6
	local.get	5
	local.get	6
	i32.add 
	local.set	7
	local.get	7
	local.set	8
	i32.const	.L__unnamed_1
	local.set	9
	local.get	9
	local.set	10
	local.get	8
	local.get	10
	local.get	1
	local.get	2
	call	_ZN3std2rt19lang_start_internal17h0a36e5f1c84a3c30E
	local.set	11
	local.get	11
	call	_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E
	local.set	12
	i32.const	16
	local.set	13
	local.get	5
	local.get	13
	i32.add 
	local.set	14
	local.get	14
	global.set	__stack_pointer
	local.get	12
	return
	end_function
.Lfunc_end1:
	.size	_ZN3std2rt10lang_start17hf2384963b248006fE, .Lfunc_end1-_ZN3std2rt10lang_start17hf2384963b248006fE

	.section	".text._ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE","",@
	.type	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE,@function
_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE:
	.functype	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE (i32) -> (i32)
	.local  	i32, i32
	local.get	0
	i32.load	0
	local.set	1
	local.get	1
	call	_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h3cf28cee3a7a5851E
	call	_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E
	local.set	2
	local.get	2
	return
	end_function
.Lfunc_end2:
	.size	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE, .Lfunc_end2-_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE

	.section	".text._ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E","",@
	.type	_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E,@function
_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E:
	.functype	_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E (i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	local.get	0
	i32.load	0
	local.set	4
	local.get	4
	call	_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E
	local.set	5
	i32.const	16
	local.set	6
	local.get	3
	local.get	6
	i32.add 
	local.set	7
	local.get	7
	global.set	__stack_pointer
	local.get	5
	return
	end_function
.Lfunc_end3:
	.size	_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E, .Lfunc_end3-_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E

	.section	.text._ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E,"",@
	.type	_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E,@function
_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E:
	.functype	_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E (i32) -> ()
	.local  	i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	local.get	0
	call_indirect	 () -> ()
	i32.const	16
	local.set	4
	local.get	3
	local.get	4
	i32.add 
	local.set	5
	local.get	5
	global.set	__stack_pointer
	return
	end_function
.Lfunc_end4:
	.size	_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E, .Lfunc_end4-_ZN4core3ops8function6FnOnce9call_once17h2aaed4c85d38c4e1E

	.section	.text._ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E,"",@
	.type	_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E,@function
_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E:
	.functype	_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E (i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	local.get	3
	local.get	0
	i32.store	4
	i32.const	4
	local.set	4
	local.get	3
	local.get	4
	i32.add 
	local.set	5
	local.get	5
	local.set	6
	local.get	6
	call	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE
	local.set	7
	i32.const	16
	local.set	8
	local.get	3
	local.get	8
	i32.add 
	local.set	9
	local.get	9
	global.set	__stack_pointer
	local.get	7
	return
	end_function
.Lfunc_end5:
	.size	_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E, .Lfunc_end5-_ZN4core3ops8function6FnOnce9call_once17h445167c6d9b260b6E

	.section	".text._ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E","",@
	.type	_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E,@function
_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E:
	.functype	_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E (i32) -> ()
	return
	end_function
.Lfunc_end6:
	.size	_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E, .Lfunc_end6-_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E

	.section	.text._ZN4core4hint9black_box17h77f9490a0e4cf303E,"",@
	.type	_ZN4core4hint9black_box17h77f9490a0e4cf303E,@function
_ZN4core4hint9black_box17h77f9490a0e4cf303E:
	.functype	_ZN4core4hint9black_box17h77f9490a0e4cf303E () -> ()
	.local  	i32
	#APP
	#NO_APP
	return
	end_function
.Lfunc_end7:
	.size	_ZN4core4hint9black_box17h77f9490a0e4cf303E, .Lfunc_end7-_ZN4core4hint9black_box17h77f9490a0e4cf303E

	.section	".text._ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E","",@
	.type	_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E,@function
_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E:
	.functype	_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E (i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	local.get	3
	local.get	0
	i32.store	12
	i32.const	0
	local.set	4
	block   	
	block   	
	local.get	4
	br_table 	{0, 1, 0}
.LBB8_1:
	end_block
	local.get	3
	i32.load	12
	local.set	5
	i32.const	16
	local.set	6
	local.get	3
	local.get	6
	i32.add 
	local.set	7
	local.get	7
	global.set	__stack_pointer
	local.get	5
	return
.LBB8_2:
	end_block
	call	_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE
	unreachable
	unreachable
	end_function
.Lfunc_end8:
	.size	_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E, .Lfunc_end8-_ZN4core6result19Result$LT$T$C$E$GT$7into_ok17h8a4fee01cf9c2012E

	.section	".text._ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE","",@
	.type	_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE,@function
_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE:
	.functype	_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE () -> ()
	unreachable
	unreachable
	end_function
.Lfunc_end9:
	.size	_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE, .Lfunc_end9-_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE

	.section	".text._ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE","",@
	.type	_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE,@function
_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE:
	.functype	_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE () -> ()
	call	_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17hb577050edc828c0bE
	unreachable
	unreachable
	end_function
.Lfunc_end10:
	.size	_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE, .Lfunc_end10-_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h9ed26cf415f4bccfE

	.section	".text._ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E","",@
	.type	_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E,@function
_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E:
	.functype	_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E () -> (i32)
	.local  	i32, i32, i32, i32
	i32.const	0
	local.set	0
	i32.const	1
	local.set	1
	local.get	0
	local.get	1
	i32.and 
	local.set	2
	local.get	2
	call	_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E
	local.set	3
	local.get	3
	return
	end_function
.Lfunc_end11:
	.size	_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E, .Lfunc_end11-_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h9d4d7c5bc2499379E

	.section	".text._ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E","",@
	.type	_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E,@function
_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E:
	.functype	_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E (i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	local.get	0
	local.set	4
	local.get	3
	local.get	4
	i32.store8	15
	i32.const	15
	local.set	5
	local.get	3
	local.get	5
	i32.add 
	local.set	6
	local.get	6
	local.set	7
	local.get	7
	call	_ZN3std3sys4wasm7process8ExitCode6as_i3217h695c859b57e9a521E
	local.set	8
	i32.const	16
	local.set	9
	local.get	3
	local.get	9
	i32.add 
	local.set	10
	local.get	10
	global.set	__stack_pointer
	local.get	8
	return
	end_function
.Lfunc_end12:
	.size	_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E, .Lfunc_end12-_ZN68_$LT$std..process..ExitCode$u20$as$u20$std..process..Termination$GT$6report17hc25c45557c6cb2e4E

	.section	.text._ZN2mt5hello17h09b6bb040b2cac63E,"",@
	.type	_ZN2mt5hello17h09b6bb040b2cac63E,@function
_ZN2mt5hello17h09b6bb040b2cac63E:
	.functype	_ZN2mt5hello17h09b6bb040b2cac63E (i32) -> (i32)
	.local  	i32, i32, i32, i32, i32, i64, i64, i32, i32, i32, i64, i64, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32
	global.get	__stack_pointer
	local.set	1
	i32.const	16
	local.set	2
	local.get	1
	local.get	2
	i32.sub 
	local.set	3
	local.get	3
	global.set	__stack_pointer
	i32.const	1
	local.set	4
	local.get	0
	local.get	4
	i32.gt_u
	drop
	local.get	0
	local.set	5
	block   	
	block   	
	block   	
	block   	
	block   	
	block   	
	local.get	5
	br_table 	{1, 2, 0}
.LBB13_1:
	end_block
	local.get	0
	i64.extend_i32_s
	local.set	6
	local.get	6
	local.get	6
	i64.mul 
	local.set	7
	local.get	7
	i32.wrap_i64
	local.set	8
	i32.const	31
	local.set	9
	local.get	8
	local.get	9
	i32.shr_s
	local.set	10
	i64.const	32
	local.set	11
	local.get	7
	local.get	11
	i64.shr_u
	local.set	12
	local.get	12
	i32.wrap_i64
	local.set	13
	local.get	13
	local.get	10
	i32.ne  
	local.set	14
	i32.const	1
	local.set	15
	local.get	14
	local.get	15
	i32.and 
	local.set	16
	local.get	16
	br_if   	3
	br      	2
.LBB13_2:
	end_block
	i32.const	1
	local.set	17
	local.get	3
	local.get	17
	i32.store	12
	br      	3
.LBB13_3:
	end_block
	i32.const	4294967295
	local.set	18
	local.get	3
	local.get	18
	i32.store	12
	br      	2
.LBB13_4:
	end_block
	local.get	3
	local.get	8
	i32.store	12
	br      	1
.LBB13_5:
	end_block
	i32.const	str.0
	local.set	19
	local.get	19
	local.set	20
	i32.const	33
	local.set	21
	i32.const	.L__unnamed_2
	local.set	22
	local.get	22
	local.set	23
	local.get	20
	local.get	21
	local.get	23
	call	_ZN4core9panicking5panic17hb05521048dcb55f3E
	unreachable
.LBB13_6:
	end_block
	local.get	3
	i32.load	12
	local.set	24
	i32.const	16
	local.set	25
	local.get	3
	local.get	25
	i32.add 
	local.set	26
	local.get	26
	global.set	__stack_pointer
	local.get	24
	return
	end_function
.Lfunc_end13:
	.size	_ZN2mt5hello17h09b6bb040b2cac63E, .Lfunc_end13-_ZN2mt5hello17h09b6bb040b2cac63E

	.section	.text._ZN2mt4main17hdf8d4252388e3c5aE,"",@
	.type	_ZN2mt4main17hdf8d4252388e3c5aE,@function
_ZN2mt4main17hdf8d4252388e3c5aE:
	.functype	_ZN2mt4main17hdf8d4252388e3c5aE () -> ()
	.local  	i32
	i32.const	3
	local.set	0
	local.get	0
	call	_ZN2mt5hello17h09b6bb040b2cac63E
	drop
	return
	end_function
.Lfunc_end14:
	.size	_ZN2mt4main17hdf8d4252388e3c5aE, .Lfunc_end14-_ZN2mt4main17hdf8d4252388e3c5aE

	.section	.text.main,"",@
	.globl	main
	.type	main,@function
main:
	.functype	main (i32, i32) -> (i32)
	.local  	i32, i32
	i32.const	_ZN2mt4main17hdf8d4252388e3c5aE
	local.set	2
	local.get	2
	local.get	0
	local.get	1
	call	_ZN3std2rt10lang_start17hf2384963b248006fE
	local.set	3
	local.get	3
	return
	end_function
.Lfunc_end15:
	.size	main, .Lfunc_end15-main

	.type	.L__unnamed_1,@object
	.section	.rodata..L__unnamed_1,"",@
	.p2align	2
.L__unnamed_1:
	.int32	_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17had514ba614eee368E
	.asciz	"\004\000\000\000\004\000\000"
	.int32	_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h2c70f2fcca5f8800E
	.int32	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE
	.int32	_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h2e14eaf2490f108dE
	.size	.L__unnamed_1, 24

	.type	.L__unnamed_3,@object
	.section	.rodata..L__unnamed_3,"",@
.L__unnamed_3:
	.ascii	"mt.rs"
	.size	.L__unnamed_3, 5

	.type	.L__unnamed_2,@object
	.section	.rodata..L__unnamed_2,"",@
	.p2align	2
.L__unnamed_2:
	.int32	.L__unnamed_3
	.asciz	"\005\000\000\000\005\000\000\000\016\000\000"
	.size	.L__unnamed_2, 16

	.type	str.0,@object
	.section	.rodata.str.0,"",@
	.p2align	4
str.0:
	.ascii	"attempt to multiply with overflow"
	.size	str.0, 33

	.no_dead_strip	__indirect_function_table
