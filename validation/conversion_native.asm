ifndef X64
.686
.model flat,C
endif
option casemap:none
include listing6_conversion.inc
.data
PUBLIC ConversionObservation, ConversionData
ifdef X64
ConversionObservation QWORD 18 DUP(0)
ConversionTarget QWORD 0
ConversionData QWORD 0
else
ConversionObservation DWORD 18 DUP(0)
ConversionData DWORD 0
endif
.code
CODEWORD MACRO header, field
PUBLIC field
ifdef X64
header db 48h,0a3h
field QWORD 0
else
header db 0a3h
field DWORD 0
endif
ENDM
PUBLIC ConversionBegin, ConversionEnd
ConversionBegin LABEL BYTE
CODEWORD ConversionSourceOwner0, ConversionSource0
PUBLIC ConversionRun0, ConversionStop0
ConversionRun0 LABEL BYTE
    USEWORDCOPY ConversionSource0, ConversionData
ConversionStop0 LABEL BYTE
    ret
    db 7 DUP(90h)
PUBLIC ConversionRun1, ConversionStop1
ConversionRun1 LABEL BYTE
    USEWORDCOPY ConversionSource1, ConversionData
ConversionStop1 LABEL BYTE
    ret
CODEWORD ConversionSourceOwner1, ConversionSource1
    db 7 DUP(90h)
CODEWORD ConversionDestinationOwner2, ConversionDestination2
PUBLIC ConversionRun2, ConversionStop2
ConversionRun2 LABEL BYTE
    USEWORDCOPY ConversionData, ConversionDestination2
ConversionStop2 LABEL BYTE
    ret
    db 7 DUP(90h)
PUBLIC ConversionRun3, ConversionStop3
ConversionRun3 LABEL BYTE
    USEWORDCOPY ConversionData, ConversionDestination3
ConversionStop3 LABEL BYTE
    ret
CODEWORD ConversionDestinationOwner3, ConversionDestination3
    db 7 DUP(90h)
CODEWORD ConversionSourceOwner4, ConversionSource4
PUBLIC ConversionRun4, ConversionStop4
ConversionRun4 LABEL BYTE
    USEWORDCOPY ConversionSource4, ConversionDestination4
ConversionStop4 LABEL BYTE
    ret
CODEWORD ConversionDestinationOwner4, ConversionDestination4
    db 7 DUP(90h)
CODEWORD ConversionDestinationOwner5, ConversionDestination5
PUBLIC ConversionRun5, ConversionStop5
ConversionRun5 LABEL BYTE
    USEWORDCOPY ConversionSource5, ConversionDestination5
ConversionStop5 LABEL BYTE
    ret
CODEWORD ConversionSourceOwner5, ConversionSource5
    db 7 DUP(90h)
ConversionEnd LABEL BYTE
PUBLIC ConversionInvoke
ConversionInvoke PROC
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
    mov [ConversionTarget],rcx
    mov rax,rdx
    mov [ConversionObservation+136],rsp
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
    call QWORD PTR [ConversionTarget]
    mov [ConversionObservation],rax
    mov [ConversionObservation+8],rsp
    mov [ConversionObservation+16],rbx
    mov [ConversionObservation+24],rcx
    mov [ConversionObservation+32],rdx
    mov [ConversionObservation+40],rsi
    mov [ConversionObservation+48],rdi
    mov [ConversionObservation+56],rbp
    mov [ConversionObservation+64],r8
    mov [ConversionObservation+72],r9
    mov [ConversionObservation+80],r10
    mov [ConversionObservation+88],r11
    mov [ConversionObservation+96],r12
    mov [ConversionObservation+104],r13
    mov [ConversionObservation+112],r14
    mov [ConversionObservation+120],r15
    pushfq
    pop QWORD PTR [ConversionObservation+128]
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
    mov [ConversionObservation+68],esp
    bt edx,0
    mov ebx,013579bdfh
    mov ecx,02468ace0h
    mov edx,0badc0deh
    mov esi,011223344h
    mov edi,055667788h
    mov ebp,076543210h
    call DWORD PTR [esp+20]
    mov [ConversionObservation],eax
    mov [ConversionObservation+4],esp
    mov [ConversionObservation+8],ebx
    mov [ConversionObservation+12],ecx
    mov [ConversionObservation+16],edx
    mov [ConversionObservation+20],esi
    mov [ConversionObservation+24],edi
    mov [ConversionObservation+28],ebp
    pushfd
    pop DWORD PTR [ConversionObservation+64]
    pop ebp
    pop edi
    pop esi
    pop ebx
endif
    ret
ConversionInvoke ENDP
END
