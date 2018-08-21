.text
	.global entry_point

entry_point:
	push %rbp	# save stack frame for C convention
	mov %rsp, %rbp

	# beginning generated code
	movq $0, %rbx
	movq $1, %rcx
	subq %rcx, %rbx
	movq $2, %rcx
	movq $2, %rdi
	addq %rdi, %rcx
	movq %rcx, %rax
	cqto
	idivq %rbx
	movq %rax, %rbx
	movq %rbx, %rax
	# end generated code
	# %rax contains the result

	mov %rbp, %rsp	# reset frame
	pop %rbp
	ret



