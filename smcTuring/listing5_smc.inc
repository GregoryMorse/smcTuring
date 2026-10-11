; Listing 5 local cursor-field correction. DF=0; complete separate buffers
; and cursor words; no pointer wrap; size must fit the SUB immediate.
include pure_smc.inc
ifdef X64
TRANSFER_CURSOR_OFFS EQU 0
TRANSFER_SI TEXTEQU <rsi>
TRANSFER_DI TEXTEQU <rdi>
else
TRANSFER_CURSOR_OFFS EQU 6
TRANSFER_SI TEXTEQU <esi>
TRANSFER_DI TEXTEQU <edi>
endif
DEFDATA_TRANSFER MACRO labelname:req, initial:req
ifdef X64
    DEFADDR labelname, initial
else
labelname: mov DWORD PTR [labelname+6],initial
endif
ENDM
MOVSMACRO MACRO size:req
ifdef X64
    REPT size / 8
        movsq
    ENDM
    IF (size MOD 8) AND 4
        movsd
    ENDIF
else
    REPT size / 4
        movsd
    ENDM
endif
    IF (size MOD 4) AND 2
        movsw
    ENDIF
    IF size AND 1
        movsb
    ENDIF
ENDM
TRANSFERDATA MACRO source:req,sourceinit:req,dest:req,destinit:req,size:req
    DEFDATA_TRANSFER source,sourceinit
    xchg TRANSFER_SI,SMC_WORD PTR [source+TRANSFER_CURSOR_OFFS]
    DEFDATA_TRANSFER dest,destinit
    xchg TRANSFER_DI,SMC_WORD PTR [dest+TRANSFER_CURSOR_OFFS]
source&CopyBegin LABEL BYTE
    MOVSMACRO size
source&CopyEnd LABEL BYTE
    xchg TRANSFER_SI,SMC_WORD PTR [source+TRANSFER_CURSOR_OFFS]
    sub SMC_WORD PTR [source+TRANSFER_CURSOR_OFFS],size
    xchg TRANSFER_DI,SMC_WORD PTR [dest+TRANSFER_CURSOR_OFFS]
    sub SMC_WORD PTR [dest+TRANSFER_CURSOR_OFFS],size
ENDM
