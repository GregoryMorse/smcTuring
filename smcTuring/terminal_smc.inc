; Minimal Listing 2 DOHALT correction; host observes the following PC.
; DWORD C7/05 has immediate offset six and length ten in both modes.
SMC_DOHALT MACRO labelname
labelname LABEL BYTE
    mov DWORD PTR [labelname+6], 0
ENDM
