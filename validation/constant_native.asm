.686
.model flat, C
option casemap:none
.data
PUBLIC ConstantObservation
ConstantObservation DWORD 10 DUP(0)
.code
PUBLIC ConstantInvoke
; Host setup/observation and CALL/RET surround the pure emitted straight line.
ConstantInvoke PROC
    push ebx
    push esi
    push edi
    push ebp
    mov eax, [esp+24]
    mov edx, [esp+28]
    mov [ConstantObservation+36], esp
    bt edx, 0
    mov ebx, 13579bdfh
    mov ecx, 2468ace0h
    mov edx, 0badc0deh
    mov esi, 11223344h
    mov edi, 55667788h
    mov ebp, 76543210h
    call dword ptr [esp+20]
    mov [ConstantObservation+0], eax
    mov [ConstantObservation+4], esp
    mov [ConstantObservation+8], ebx
    mov [ConstantObservation+12], ecx
    mov [ConstantObservation+16], edx
    mov [ConstantObservation+20], esi
    mov [ConstantObservation+24], edi
    mov [ConstantObservation+28], ebp
    pushfd
    pop dword ptr [ConstantObservation+32]
    mov esp, [ConstantObservation+36]
    pop ebp
    pop edi
    pop esi
    pop ebx
    ret
ConstantInvoke ENDP
END
