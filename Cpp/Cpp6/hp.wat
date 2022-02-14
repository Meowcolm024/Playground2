	.text
	.file	"hp.cpp"
	.section	.text._Z3byei,"",@
	.hidden	_Z3byei                         # -- Begin function _Z3byei
	.globl	_Z3byei
	.type	_Z3byei,@function
_Z3byei:                                # @_Z3byei
	.functype	_Z3byei (i32) -> (i32)
	.local  	i64, i64, i64, i32, i32, i32, i32, i32, i32, i32, i32, i32
# %bb.0:
	global.get	__stack_pointer
	local.set	1
	i64.const	16
	local.set	2
	local.get	1
	local.get	2
	i64.sub 
	local.set	3
	local.get	3
	local.get	0
	i32.store	12
	local.get	3
	i32.load	12
	local.set	4
	i32.const	10
	local.set	5
	local.get	4
	local.get	5
	i32.mul 
	local.set	6
	local.get	3
	local.get	6
	i32.store	8
	local.get	3
	i32.load	12
	local.set	7
	i32.const	5
	local.set	8
	local.get	7
	local.get	8
	i32.add 
	local.set	9
	local.get	3
	local.get	9
	i32.store	4
	local.get	3
	i32.load	8
	local.set	10
	local.get	3
	i32.load	4
	local.set	11
	local.get	10
	local.get	11
	i32.add 
	local.set	12
	local.get	12
	return
	end_function
.Lfunc_end0:
	.size	_Z3byei, .Lfunc_end0-_Z3byei
                                        # -- End function
	.section	.text._Z5helloii,"",@
	.hidden	_Z5helloii                      # -- Begin function _Z5helloii
	.globl	_Z5helloii
	.type	_Z5helloii,@function
_Z5helloii:                             # @_Z5helloii
	.functype	_Z5helloii (i32, i32) -> (i32)
	.local  	i64, i64, i64, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32
# %bb.0:
	global.get	__stack_pointer
	local.set	2
	i64.const	16
	local.set	3
	local.get	2
	local.get	3
	i64.sub 
	local.set	4
	local.get	4
	local.get	0
	i32.store	12
	local.get	4
	local.get	1
	i32.store	8
	i32.const	0
	local.set	5
	local.get	4
	local.get	5
	i32.store	4
	local.get	4
	i32.load	12
	local.set	6
	local.get	4
	i32.load	8
	local.set	7
	local.get	6
	local.set	8
	local.get	7
	local.set	9
	local.get	8
	local.get	9
	i32.gt_s
	local.set	10
	i32.const	1
	local.set	11
	local.get	10
	local.get	11
	i32.and 
	local.set	12
	block   	
	block   	
	local.get	12
	i32.eqz
	br_if   	0                               # 0: down to label1
# %bb.1:
	local.get	4
	i32.load	12
	local.set	13
	i32.const	10
	local.set	14
	local.get	13
	local.get	14
	i32.mul 
	local.set	15
	local.get	4
	local.get	15
	i32.store	4
	br      	1                               # 1: down to label0
.LBB1_2:
	end_block                               # label1:
	local.get	4
	i32.load	12
	local.set	16
	i32.const	10
	local.set	17
	local.get	16
	local.get	17
	i32.div_s
	local.set	18
	local.get	4
	local.get	18
	i32.store	4
.LBB1_3:
	end_block                               # label0:
	local.get	4
	i32.load	4
	local.set	19
	local.get	19
	return
	end_function
.Lfunc_end1:
	.size	_Z5helloii, .Lfunc_end1-_Z5helloii
                                        # -- End function
	.ident	"Homebrew clang version 12.0.1"
	.globaltype	__stack_pointer, i64
	.section	.custom_section.producers,"",@
	.int8	1
	.int8	12
	.ascii	"processed-by"
	.int8	1
	.int8	14
	.ascii	"Homebrew clang"
	.int8	6
	.ascii	"12.0.1"
	.section	.text._Z5helloii,"",@
