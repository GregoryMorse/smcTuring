// GNU assembler port of the comparison routines in tm.asm.
// Linux and Intel macOS use the System V ABI; operands and links are pointer-sized.
#ifdef __APPLE__
#define C_SYMBOL(name) _##name
#else
#define C_SYMBOL(name) name
#endif
#if defined(__x86_64__)
#define WORD 8
#define PTR qword ptr
#define X rax
#define Y rbx
#define M rdi
#define L r10
#define T rcx
#define S rdx
#define N r8
#define SCRATCH r9
#define TRANSITION T
#define INPUT S
#define LEFT N
#define RIGHT_PTR [rsp]
#define LEFT_PTR [rsp + 8]
#elif defined(__i386__)
#define WORD 4
#define PTR dword ptr
#define X eax
#define Y ebx
#define M ecx
#define L edi
#define T edi
#define S edx
#define N esi
#define SCRATCH [ebp + 20]
#define TRANSITION [ebp + 8]
#define INPUT [ebp + 12]
#define LEFT [ebp + 16]
#define RIGHT_PTR [ebp + 24]
#define LEFT_PTR [ebp + 28]
#else
#error "The assembly comparison simulators require x86 or x86-64."
#endif
#define R L
#define Z Y
#define D Y
#define H M

.intel_syntax noprefix
.text
.p2align 4
.globl C_SYMBOL(MovTM)
#ifndef __APPLE__
.type C_SYMBOL(MovTM), @function
#endif
C_SYMBOL(MovTM):
    .cfi_startproc
#ifdef __x86_64__
    push rbx
    .cfi_adjust_cfa_offset 8
    .cfi_offset rbx, -16
    sub rsp, 16
    .cfi_adjust_cfa_offset 16
    // Save the two mutable tape-list heads, then map SysV arguments to
    // the logical registers used by the original MOV body.
    mov RIGHT_PTR, r8
    mov LEFT_PTR, r9
    mov r11, rcx
    mov r10, rdx
    mov rcx, rdi
    mov rdx, rsi
    mov r8, r10
    mov r9, r11
#else
    push ebp
    .cfi_adjust_cfa_offset 4
    .cfi_offset ebp, -8
    mov ebp, esp
    .cfi_def_cfa_register ebp
    push ebx
    .cfi_offset ebx, -12
    push esi
    .cfi_offset esi, -16
    push edi
    .cfi_offset edi, -20
#endif
    mov T, TRANSITION
    mov S, INPUT
    mov N, LEFT
Lmov_start:
    mov X, [T]
    mov X, [X]
    mov Y, [S]
    // Load the scratch pointer explicitly on both ABIs.
    mov M, SCRATCH
    mov PTR [M + Y * WORD], 0
    mov PTR [M + X * WORD], WORD
    mov M, [M + Y * WORD]

    mov X, [T]
    mov X, [X + WORD]
    mov X, [X]
    mov Y, [S]
    mov [N], Y
    mov [N + WORD], X
    mov Z, [N + M]
    mov [S], Z

    mov D, [T]
    mov D, [D + WORD]
    mov D, [D + WORD]
    mov D, [D]

    mov R, RIGHT_PTR
    mov [N], R
    mov L, LEFT_PTR
    mov [N + WORD], L
    mov X, [N + D]
    mov [S + WORD], X
    mov [N], L
    mov [N + WORD], S
    mov L, [N + D]
    mov LEFT_PTR, L
    mov [N], S
    mov R, RIGHT_PTR
    mov [N + WORD], R
    mov R, [N + D]
    mov RIGHT_PTR, R

    mov PTR [N], WORD
    mov PTR [N + WORD], 0
    mov X, [N + D]
    mov [N], X
    mov [N + WORD], D
    mov D, [N + M]

    mov L, LEFT_PTR
    mov [N], L
    mov R, RIGHT_PTR
    mov [N + WORD], R
    mov S, [N + D]
    mov X, [S + WORD]
    mov [N], X
    mov L, LEFT_PTR
    mov [N + WORD], L
    mov L, [N + D]
    mov LEFT_PTR, L
    mov R, RIGHT_PTR
    mov [N], R
    mov [N + WORD], X
    mov R, [N + D]
    mov RIGHT_PTR, R

    mov T, TRANSITION
    mov X, [T + WORD]
    mov Y, [T]
    mov Y, [Y + WORD]
    mov Y, [Y + WORD]
    mov Y, [Y + WORD]
    mov Y, [Y]
    mov [N], X
    mov [N + WORD], Y
    mov T, [N + M]
    mov TRANSITION, T

    mov X, [T]
    mov PTR [N], WORD
    mov PTR [T], 0
    mov H, [N]
    mov [T], X
    mov PTR [N], 0
    mov [N + WORD], N
    mov X, [N + H]
    cmp X, 0
    je Lmov_finish
    mov X, [X]
    jmp Lmov_start
Lmov_finish:
#ifdef __x86_64__
    add rsp, 16
    .cfi_adjust_cfa_offset -16
    pop rbx
    .cfi_adjust_cfa_offset -8
    .cfi_restore rbx
#else
    pop edi
    .cfi_restore edi
    pop esi
    .cfi_restore esi
    pop ebx
    .cfi_restore ebx
    pop ebp
    .cfi_def_cfa esp, 4
    .cfi_restore ebp
#endif
    ret
    .cfi_endproc
#ifndef __APPLE__
.size C_SYMBOL(MovTM), .-C_SYMBOL(MovTM)
#endif

.p2align 4
.globl C_SYMBOL(AsmTM)
#ifndef __APPLE__
.type C_SYMBOL(AsmTM), @function
#endif
C_SYMBOL(AsmTM):
    .cfi_startproc
#ifdef __x86_64__
    // rdi = transition table, rsi = tape, r8b = initial state.
    // The historical third/fourth parameters are local cursor placeholders.
    mov rax, rdi
    mov rdx, rsi
Lflat_begin:
    cmp byte ptr [rax], r8b
    jne Lflat_next
    mov r9b, [rax + 1]
    cmp r9b, [rdx]
    jne Lflat_next
    mov r8b, [rax + 4]
    mov r9b, [rax + 2]
    mov [rdx], r9b
    movsx r10, byte ptr [rax + 3]
    add rdx, r10
    cmp r8b, '2'
    je Lflat_finish
    mov rax, rdi
    jmp Lflat_begin
Lflat_next:
    add rax, 5
    cmp rax, rsi
    jne Lflat_begin
#else
    push ebx
    .cfi_adjust_cfa_offset 4
    .cfi_offset ebx, -8
    push esi
    .cfi_adjust_cfa_offset 4
    .cfi_offset esi, -12
    push edi
    .cfi_adjust_cfa_offset 4
    .cfi_offset edi, -16
    mov ebx, [esp + 16]
    mov esi, [esp + 20]
    movzx ecx, byte ptr [esp + 32]
    mov eax, ebx
    mov edi, esi
Lflat_begin:
    cmp byte ptr [eax], cl
    jne Lflat_next
    mov dl, [eax + 1]
    cmp dl, [edi]
    jne Lflat_next
    mov cl, [eax + 4]
    mov dl, [eax + 2]
    mov [edi], dl
    movsx edx, byte ptr [eax + 3]
    add edi, edx
    cmp cl, '2'
    je Lflat_finish
    mov eax, ebx
    jmp Lflat_begin
Lflat_next:
    add eax, 5
    cmp eax, esi
    jne Lflat_begin
#endif
Lflat_finish:
#ifdef __i386__
    pop edi
    .cfi_adjust_cfa_offset -4
    .cfi_restore edi
    pop esi
    .cfi_adjust_cfa_offset -4
    .cfi_restore esi
    pop ebx
    .cfi_adjust_cfa_offset -4
    .cfi_restore ebx
#endif
    ret
    .cfi_endproc
#ifndef __APPLE__
.size C_SYMBOL(AsmTM), .-C_SYMBOL(AsmTM)
#endif

.p2align 4
.globl C_SYMBOL(AsmListTM)
#ifndef __APPLE__
.type C_SYMBOL(AsmListTM), @function
#endif
C_SYMBOL(AsmListTM):
    .cfi_startproc
#ifdef __x86_64__
    mov rax, rdi
    mov rdx, rsi
Llist_begin:
    mov r9, [rax + 8]
    cmp r9b, [rdx]
    jne Llist_next
    mov r9, [rax + 16]
    mov [rdx], r9b
    movsx r10, byte ptr [rax + 24]
    add rdx, r10
    mov rax, [rax + 32]
    jmp Llist_check
Llist_next:
    mov rax, [rax]
Llist_check:
    test rax, rax
    jne Llist_begin
#else
    mov eax, [esp + 4]
    mov edx, [esp + 8]
Llist_begin:
    mov ecx, [eax + 4]
    cmp cl, [edx]
    jne Llist_next
    mov ecx, [eax + 8]
    mov [edx], cl
    movsx ecx, byte ptr [eax + 12]
    add edx, ecx
    mov eax, [eax + 16]
    jmp Llist_check
Llist_next:
    mov eax, [eax]
Llist_check:
    test eax, eax
    jne Llist_begin
#endif
    ret
    .cfi_endproc
#ifndef __APPLE__
.size C_SYMBOL(AsmListTM), .-C_SYMBOL(AsmListTM)
#endif

#ifdef __APPLE__
.subsections_via_symbols
#else
.section .note.GNU-stack,"",@progbits
#endif
