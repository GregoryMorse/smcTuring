; Printed DEFDATA32: a live DWORD operand stores itself without resetting it.
; The label is the ten-byte C7/05 instruction entry; its operand is label+6.
SMC_DEFDATA32 MACRO labelname:req, data:req
labelname LABEL BYTE
    mov DWORD PTR [labelname+6],data
ENDM
