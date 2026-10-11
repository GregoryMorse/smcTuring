ifndef X64
.model flat, C
endif
option casemap:none
.data
HalfFlags dq 0
.code
HalfBegin:
ifdef X64
HalfMove PROC
    mov rax, rcx
    bt rdx, 0
else
HalfMove PROC seed:DWORD, incoming:DWORD
    mov eax, seed
    bt incoming, 0
endif
HalfMovePure:
    xchg eax, dword ptr [HalfSourceLow+6]
    mov dword ptr [HalfTargetLow+6], eax
    xchg eax, dword ptr [HalfSourceLow+6]
    xchg eax, dword ptr [HalfSourceHigh+6]
    mov dword ptr [HalfTargetHigh+6], eax
    xchg eax, dword ptr [HalfSourceHigh+6]
HalfMovePureEnd:
ifdef X64
    pushfq
    pop qword ptr [HalfFlags]
else
    pushfd
    pop dword ptr [HalfFlags]
endif
    ret
HalfMove ENDP
ifdef X64
HalfXor PROC
    mov rax, rcx
    bt rdx, 0
else
HalfXor PROC seed:DWORD, incoming:DWORD
    mov eax, seed
    bt incoming, 0
endif
HalfXorPure:
    xchg eax, dword ptr [HalfSourceLow+6]
    xor dword ptr [HalfTargetLow+6], eax
    xchg eax, dword ptr [HalfSourceLow+6]
    xchg eax, dword ptr [HalfSourceHigh+6]
    xor dword ptr [HalfTargetHigh+6], eax
    xchg eax, dword ptr [HalfSourceHigh+6]
HalfXorPureEnd:
ifdef X64
    pushfq
    pop qword ptr [HalfFlags]
else
    pushfd
    pop dword ptr [HalfFlags]
endif
    ret
HalfXor ENDP
ifdef X64
HalfAnd PROC
    mov rax, rcx
    bt rdx, 0
else
HalfAnd PROC seed:DWORD, incoming:DWORD
    mov eax, seed
    bt incoming, 0
endif
HalfAndPure:
    xchg eax, dword ptr [HalfSourceLow+6]
    and dword ptr [HalfTargetLow+6], eax
    xchg eax, dword ptr [HalfSourceLow+6]
    xchg eax, dword ptr [HalfSourceHigh+6]
    and dword ptr [HalfTargetHigh+6], eax
    xchg eax, dword ptr [HalfSourceHigh+6]
HalfAndPureEnd:
ifdef X64
    pushfq
    pop qword ptr [HalfFlags]
else
    pushfd
    pop dword ptr [HalfFlags]
endif
    ret
HalfAnd ENDP
ifdef X64
HalfOr PROC
    mov rax, rcx
    bt rdx, 0
else
HalfOr PROC seed:DWORD, incoming:DWORD
    mov eax, seed
    bt incoming, 0
endif
HalfOrPure:
    xchg eax, dword ptr [HalfSourceLow+6]
    or dword ptr [HalfTargetLow+6], eax
    xchg eax, dword ptr [HalfSourceLow+6]
    xchg eax, dword ptr [HalfSourceHigh+6]
    or dword ptr [HalfTargetHigh+6], eax
    xchg eax, dword ptr [HalfSourceHigh+6]
HalfOrPureEnd:
ifdef X64
    pushfq
    pop qword ptr [HalfFlags]
else
    pushfd
    pop dword ptr [HalfFlags]
endif
    ret
HalfOr ENDP
ifdef X64
HalfNot PROC
    mov rax, rcx
    bt rdx, 0
else
HalfNot PROC seed:DWORD, incoming:DWORD
    mov eax, seed
    bt incoming, 0
endif
HalfNotPure:
    not dword ptr [HalfTargetLow+6]
    not dword ptr [HalfTargetHigh+6]
HalfNotPureEnd:
ifdef X64
    pushfq
    pop qword ptr [HalfFlags]
else
    pushfd
    pop dword ptr [HalfFlags]
endif
    ret
HalfNot ENDP
GetHalfBegin PROC
ifdef X64
    lea rax, HalfBegin
else
    mov eax, OFFSET HalfBegin
endif
    ret
GetHalfBegin ENDP
GetHalfEnd PROC
ifdef X64
    lea rax, HalfEnd
else
    mov eax, OFFSET HalfEnd
endif
    ret
GetHalfEnd ENDP
GetHalfFields PROC
ifdef X64
    lea rax, HalfTargetLow
else
    mov eax, OFFSET HalfTargetLow
endif
    ret
GetHalfFields ENDP
GetHalfFlags PROC
ifdef X64
    mov rax, qword ptr [HalfFlags]
else
    mov eax, dword ptr [HalfFlags]
endif
    ret
GetHalfFlags ENDP
HalfTargetLow: mov dword ptr [HalfTargetLow+6], 0
HalfTargetHigh: mov dword ptr [HalfTargetHigh+6], 0
HalfSourceLow: mov dword ptr [HalfSourceLow+6], 0
HalfSourceHigh: mov dword ptr [HalfSourceHigh+6], 0
HalfEnd:
END
