ifndef X64
.model flat, C
endif
option casemap :none
include pure_smc.inc
.code

ifdef X64
NativeLegacy PROC
    mov qword ptr [legacyField], rdx
    mov rax, rcx
else
NativeLegacy PROC seed:DWORD, pointer:DWORD
    mov eax, pointer
    mov dword ptr [legacyField], eax
    mov eax, seed
endif
    DEFADDR_LEGACY legacyField, 0
    ret
NativeLegacy ENDP

ifdef X64
NativeCorrected PROC
    mov qword ptr [correctedField], rdx
    mov rax, rcx
else
NativeCorrected PROC seed:DWORD, pointer:DWORD
    mov eax, pointer
    mov dword ptr [correctedField], eax
    mov eax, seed
endif
    DEFADDR correctedField, 0
    ret
NativeCorrected ENDP

GetLegacyField PROC
ifdef X64
    lea rax, legacyField
else
    mov eax, OFFSET legacyField
endif
    ret
GetLegacyField ENDP

GetCorrectedField PROC
ifdef X64
    lea rax, correctedField
else
    mov eax, OFFSET correctedField
endif
    ret
GetCorrectedField ENDP

GetTargetField PROC
ifdef X64
    lea rax, targetField
else
    mov eax, OFFSET targetField
endif
    ret
GetTargetField ENDP

; A target word lives inside the address operand of a real instruction template.
; This template is storage and is not fetched during the primitive test.
    MOFFSMOV targetField, 0
END
