; Listing 6 USEWORD applied to MOV: preserve the source word and accumulator.
; Operand width equals the actual four/eight-byte source and destination field.
USEWORDCOPY MACRO sourceword, destinationword
ifdef X64
    xchg rax,QWORD PTR [sourceword]
    mov QWORD PTR [destinationword],rax
    xchg rax,QWORD PTR [sourceword]
else
    xchg eax,DWORD PTR [sourceword]
    mov DWORD PTR [destinationword],eax
    xchg eax,DWORD PTR [sourceword]
endif
ENDM
