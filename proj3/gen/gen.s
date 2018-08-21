.text
.global putchar, getchar, entry_point

################# FUNCTIONS #####################
#################################################


###################### MAIN #####################
entry_point:
	pushq %rbp	# save stack frame for calling convention
	movq %rsp, %rbp
	movq %rdi, heap(%rip)
	movq $1, %rdi
	movq $2, %rsi
	cmp %rsi, %rdi
	setg %al
	movzbq %al, %rdi
	test %rdi, %rdi
	jne if1_then
	movq $4, %rdi
	jmp if1_end
if1_then:
	movq $1, %rdi
if1_end:
	movq %rdi, %rax
	movq %rbp, %rsp	# reset frame
	popq %rbp
	ret
#################################################


#################### DATA #######################

.data
heap:	.quad 0
#################################################
