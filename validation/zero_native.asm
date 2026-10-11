ifndef X64
.686
.model flat,C
endif
option casemap:none
include listing6_smc.inc
.data
PUBLIC ZeroObservation
ifdef X64
ZeroObservation QWORD 18 DUP(0)
ZeroTarget QWORD 0
else
ZeroObservation DWORD 18 DUP(0)
endif
.code
PUBLIC ZeroPrinted, ZeroForced, ZeroInvoke
ZeroPrinted:
    xor DWORD PTR [ZeroPrinted+6],0
    ret
    db 5ah,0a5h,8 DUP(90h)
DEFZERO ZeroForced
    ret
    db 9 DUP(90h)
ZeroInvoke PROC
ifdef X64
    push rbx
    push rsi
    push rdi
    push rbp
    push r12
    push r13
    push r14
    push r15
    sub rsp,40
    mov [ZeroTarget],rcx
    mov rax,rdx
    mov [ZeroObservation+136],rsp
    bt r8,0
    mov rbx,013579bdfh
    mov rcx,02468ace0h
    mov rdx,0badc0deh
    mov rsi,011223344h
    mov rdi,055667788h
    mov rbp,076543210h
    mov r8,010203040h
    mov r9,050607080h
    mov r10,090a0b0c0h
    mov r11,0d0e0f001h
    mov r12,023456789h
    mov r13,0abcdef01h
    mov r14,031415926h
    mov r15,027182818h
    call QWORD PTR [ZeroTarget]
    mov [ZeroObservation],rax
    mov [ZeroObservation+8],rsp
    mov [ZeroObservation+16],rbx
    mov [ZeroObservation+24],rcx
    mov [ZeroObservation+32],rdx
    mov [ZeroObservation+40],rsi
    mov [ZeroObservation+48],rdi
    mov [ZeroObservation+56],rbp
    mov [ZeroObservation+64],r8
    mov [ZeroObservation+72],r9
    mov [ZeroObservation+80],r10
    mov [ZeroObservation+88],r11
    mov [ZeroObservation+96],r12
    mov [ZeroObservation+104],r13
    mov [ZeroObservation+112],r14
    mov [ZeroObservation+120],r15
    pushfq
    pop QWORD PTR [ZeroObservation+128]
    add rsp,40
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rdi
    pop rsi
    pop rbx
else
    push ebx
    push esi
    push edi
    push ebp
    mov eax,[esp+24]
    mov edx,[esp+28]
    mov [ZeroObservation+68],esp
    bt edx,0
    mov ebx,013579bdfh
    mov ecx,02468ace0h
    mov edx,0badc0deh
    mov esi,011223344h
    mov edi,055667788h
    mov ebp,076543210h
    call DWORD PTR [esp+20]
    mov [ZeroObservation],eax
    mov [ZeroObservation+4],esp
    mov [ZeroObservation+8],ebx
    mov [ZeroObservation+12],ecx
    mov [ZeroObservation+16],edx
    mov [ZeroObservation+20],esi
    mov [ZeroObservation+24],edi
    mov [ZeroObservation+28],ebp
    pushfd
    pop DWORD PTR [ZeroObservation+64]
    pop ebp
    pop edi
    pop esi
    pop ebx
endif
    ret
ZeroInvoke ENDP
END
