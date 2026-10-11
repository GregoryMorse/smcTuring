; Corrected Listing 2 storage primitive. Setup/observation are caller obligations.
; Every instruction in DEFADDR writes memory; both label and target must be code.
; The final memory is unchanged and the accumulator contains the target's word.
; The legacy definition is retained ONLY for differential regression tests.

ifdef X64
SMC_ACC TEXTEQU <rax>
SMC_WORD TEXTEQU <qword>
else
SMC_ACC TEXTEQU <eax>
SMC_WORD TEXTEQU <dword>
endif

MOFFSMOV MACRO labelname:req, addr:req
ifdef X64
    db 048h
endif
    db 0A3h
ifdef X64
labelname dq addr
else
labelname dd addr
endif
ENDM

DEFADDR MACRO labelname:req, addr:req
    xchg SMC_ACC, SMC_WORD ptr [labelname]
    mov SMC_WORD ptr [labelname], SMC_ACC
    xchg SMC_ACC, SMC_WORD ptr [SMC_ACC]
    MOFFSMOV labelname, addr
ENDM

DEFADDR_LEGACY MACRO labelname:req, addr:req
    xchg SMC_ACC, SMC_WORD ptr [labelname]
    mov SMC_WORD ptr [labelname], SMC_ACC
    mov SMC_ACC, SMC_WORD ptr [SMC_ACC]
    MOFFSMOV labelname, addr
ENDM
