; Listing 6 DEFZERO, M09: a complete imm32 owner at byte offset six.
; CNSTFRC32=80000000h forces the initial 81 /6 encoding. Patching its
; immediate to zero at runtime retains that same ten-byte instruction.
DEFZERO MACRO labelname
labelname: xor DWORD PTR [labelname+6],80000000h
ENDM
