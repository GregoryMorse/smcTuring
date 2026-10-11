.686
.model flat, C
option casemap:none
.data
PUBLIC MulObservation
MulObservation DWORD 10 DUP(0)
.code
PUBLIC MulPureBegin, MulPureEnd, MulGuardBegin, MulBodyBegin, MulFinishBegin, MulEntryCall, MulBackCall
PUBLIC MulNative, MulBegin, MulEnd, MulInputX, MulInputY, MulResult, stptr, lbl0, lbl1, lbl2, lbl3, lbl4, lbl5, lbl6, lbl7, lbl8, lbl9, lbl10, lblbody
MulBegin:
MulNative PROC
    push ebx
    push esi
    push edi
    push ebp
    mov eax, [esp+20]
    mov edx, [esp+24]
    mov [MulObservation+36], esp
    bt edx, 0
    mov ebx, 13579bdfh
    mov ecx, 2468ace0h
    mov edx, 0badc0deh
    mov esi, 11223344h
    mov edi, 55667788h
    mov ebp, 76543210h
MulPureBegin::
    mov dword ptr [lbl10+6], 0
    xchg dword ptr [MulInputX+6], eax
    mov dword ptr [lbl7+6], eax
    xchg dword ptr [MulInputX+6], eax
    xchg dword ptr [MulInputY+6], eax
    mov dword ptr [lbl8+6], eax
    xchg dword ptr [MulInputY+6], eax
    xchg dword ptr [stptr+6], esp
MulEntryCall::
    call [lbl0]
lbl0::
    xchg dword ptr [stptr+6], esp
    add dword ptr [stptr+6], 4
    xchg dword ptr [stptr+6], eax
    mov dword ptr [stptr+2], eax
    xchg dword ptr [stptr+6], eax
MulGuardBegin::
    mov dword ptr [lbl2+6], 0
    neg dword ptr [lbl8+6]
    sbb dword ptr [lbl2+6], 0
    neg dword ptr [lbl8+6]
    not dword ptr [lbl2+6]
; M07: the current AND immediate receives exit-minus-next.
    mov dword ptr [lbl1+6], lbl9-lbl3-1-4
lbl1::
    and dword ptr [lbl2+6], 80000000h
lbl2::
    xor dword ptr [lbl3+1], 80000000h
    xchg dword ptr [stptr+6], esp
lbl3::
    call [lbl3+1+4]
lblbody::
    xchg dword ptr [stptr+6], esp
    add dword ptr [stptr+6], 4
    xchg dword ptr [stptr+6], eax
    mov dword ptr [stptr+2], eax
    xchg dword ptr [stptr+6], eax
MulBodyBegin::
    mov dword ptr [lbl4+6], 1
    xchg dword ptr [lbl8+6], eax
    and dword ptr [lbl4+6], eax
    xchg dword ptr [lbl8+6], eax
    xchg dword ptr [lbl7+6], eax
    mov dword ptr [lbl6+6], eax
    xchg dword ptr [lbl7+6], eax
    mov dword ptr [lbl5+6], 0
lbl4::
    mov dword ptr [lbl4+6], 80000000h
    neg dword ptr [lbl4+6]
    sbb dword ptr [lbl5+6], 0
lbl5::
    and dword ptr [lbl6+6], 80000000h
lbl6::
    add dword ptr [lbl10+6], 80000000h
lbl7::
    mov dword ptr [lbl7+6], 80000000h
    shl dword ptr [lbl7+6], 1
lbl8::
    mov dword ptr [lbl8+6], 80000000h
    shr dword ptr [lbl8+6], 1
    xchg dword ptr [stptr+6], esp
MulBackCall::
    call [lbl0]
lbl9::
    xchg dword ptr [stptr+6], esp
    add dword ptr [stptr+6], 4
    xchg dword ptr [stptr+6], eax
    mov dword ptr [stptr+2], eax
    xchg dword ptr [stptr+6], eax
MulFinishBegin::
    mov dword ptr [lbl3+1], 0
lbl10::
    mov dword ptr [MulResult+6], 80000000h
MulPureEnd::
    mov [MulObservation+0], eax
    mov [MulObservation+4], esp
    mov [MulObservation+8], ebx
    mov [MulObservation+12], ecx
    mov [MulObservation+16], edx
    mov [MulObservation+20], esi
    mov [MulObservation+24], edi
    mov [MulObservation+28], ebp
    pushfd
    pop dword ptr [MulObservation+32]
    mov esp, [MulObservation+36]
    pop ebp
    pop edi
    pop esi
    pop ebx
    ret
MulNative ENDP
MulInputX: mov dword ptr [MulInputX+6], 0
MulInputY: mov dword ptr [MulInputY+6], 0
MulResult: mov dword ptr [MulResult+6], 0
stptr: mov dword ptr [stptr+6], OFFSET stptr+6
MulEnd:
GetMulFields PROC
    mov eax, OFFSET MulFieldTable
    ret
GetMulFields ENDP
GetMulBegin PROC
    mov eax, OFFSET MulBegin
    ret
GetMulBegin ENDP
GetMulEnd PROC
    mov eax, OFFSET MulEnd
    ret
GetMulEnd ENDP
GetMulNext PROC
    mov eax, OFFSET lbl3+5
    ret
GetMulNext ENDP
GetMulExit PROC
    mov eax, OFFSET lbl9
    ret
GetMulExit ENDP
.const
MulFieldTable DWORD OFFSET MulInputX+6, OFFSET MulInputY+6, OFFSET MulResult+6, OFFSET lbl7+6, OFFSET lbl8+6, OFFSET lbl10+6, OFFSET lbl1+6, OFFSET lbl2+6, OFFSET lbl3+1, OFFSET lbl4+6, OFFSET lbl5+6, OFFSET lbl6+6, OFFSET stptr+6, OFFSET stptr+2
END
