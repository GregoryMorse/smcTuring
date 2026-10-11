ifndef X64
.686
.model flat,C
endif
option casemap:none
include listing5_smc.inc
.data
PUBLIC TemplateRecords
ifdef X64
TemplateRecords LABEL QWORD
QWORD 0,TemplateRun0,TemplateStop0,TemplateSource0,TemplateDestination0,TemplateSize0,TemplateCursorS0+TRANSFER_CURSOR_OFFS,TemplateCursorD0+TRANSFER_CURSOR_OFFS,TemplateExternal0,TemplateExternal0Field,TemplateCursorS0CopyBegin,TemplateCursorS0CopyEnd
QWORD 1,TemplateRun1,TemplateStop1,TemplateSource1,TemplateDestination1,TemplateSize1,TemplateCursorS1+TRANSFER_CURSOR_OFFS,TemplateCursorD1+TRANSFER_CURSOR_OFFS,TemplateExternal1,TemplateExternal1Field,TemplateCursorS1CopyBegin,TemplateCursorS1CopyEnd
QWORD 2,TemplateRun2,TemplateStop2,TemplateSource2,TemplateDestination2,TemplateSize2,TemplateCursorS2+TRANSFER_CURSOR_OFFS,TemplateCursorD2+TRANSFER_CURSOR_OFFS,TemplateExternal2,TemplateExternal2Field,TemplateCursorS2CopyBegin,TemplateCursorS2CopyEnd
QWORD 3,TemplateRun3,TemplateStop3,TemplateSource3,TemplateDestination3,TemplateSize3,TemplateCursorS3+TRANSFER_CURSOR_OFFS,TemplateCursorD3+TRANSFER_CURSOR_OFFS,TemplateExternal3,TemplateExternal3Field,TemplateCursorS3CopyBegin,TemplateCursorS3CopyEnd
else
TemplateRecords LABEL DWORD
DWORD 0,TemplateRun0,TemplateStop0,TemplateSource0,TemplateDestination0,TemplateSize0,TemplateCursorS0+TRANSFER_CURSOR_OFFS,TemplateCursorD0+TRANSFER_CURSOR_OFFS,TemplateExternal0,TemplateExternal0Field,TemplateCursorS0CopyBegin,TemplateCursorS0CopyEnd
DWORD 1,TemplateRun1,TemplateStop1,TemplateSource1,TemplateDestination1,TemplateSize1,TemplateCursorS1+TRANSFER_CURSOR_OFFS,TemplateCursorD1+TRANSFER_CURSOR_OFFS,TemplateExternal1,TemplateExternal1Field,TemplateCursorS1CopyBegin,TemplateCursorS1CopyEnd
DWORD 2,TemplateRun2,TemplateStop2,TemplateSource2,TemplateDestination2,TemplateSize2,TemplateCursorS2+TRANSFER_CURSOR_OFFS,TemplateCursorD2+TRANSFER_CURSOR_OFFS,TemplateExternal2,TemplateExternal2Field,TemplateCursorS2CopyBegin,TemplateCursorS2CopyEnd
DWORD 3,TemplateRun3,TemplateStop3,TemplateSource3,TemplateDestination3,TemplateSize3,TemplateCursorS3+TRANSFER_CURSOR_OFFS,TemplateCursorD3+TRANSFER_CURSOR_OFFS,TemplateExternal3,TemplateExternal3Field,TemplateCursorS3CopyBegin,TemplateCursorS3CopyEnd
endif
.code
TemplateExternal0 LABEL BYTE
ifdef X64
DB 048h,0A3h
TemplateExternal0Field QWORD 0
else
DB 0A3h
TemplateExternal0Field DWORD 0
endif
TemplateExternal1 LABEL BYTE
ifdef X64
DB 048h,0A3h
TemplateExternal1Field QWORD 0
else
DB 0A3h
TemplateExternal1Field DWORD 0
endif
TemplateExternal2 LABEL BYTE
ifdef X64
DB 048h,0A3h
TemplateExternal2Field QWORD 0
else
DB 0A3h
TemplateExternal2Field DWORD 0
endif
TemplateExternal3 LABEL BYTE
ifdef X64
DB 048h,0A3h
TemplateExternal3Field QWORD 0
else
DB 0A3h
TemplateExternal3Field DWORD 0
endif
TemplateSource0 LABEL BYTE
ifdef X64
DB 048h,0A3h
QWORD TemplateDestination0+2
DB 048h,0A3h
QWORD TemplateExternal0Field
DB 048h,087h,005h
DWORD (TemplateDestination0+2)-(TemplateDestination0+27)
DB 048h,089h,005h
DWORD (TemplateExternal0Field)-(TemplateDestination0+34)
DB 048h,001h,005h
DWORD (TemplateDestination0+2)-(TemplateDestination0+41)
DB 048h,029h,005h
DWORD (TemplateExternal0Field)-(TemplateDestination0+48)
DB 048h,031h,005h
DWORD (TemplateDestination0+2)-(TemplateDestination0+55)
DB 048h,021h,005h
DWORD (TemplateExternal0Field)-(TemplateDestination0+62)
DB 048h,087h,025h
DWORD (TemplateDestination0+2)-(TemplateDestination0+69)
DB 048h,089h,025h
DWORD (TemplateExternal0Field)-(TemplateDestination0+76)
DB 048h,083h,01Dh
DWORD (TemplateDestination0+2)-(TemplateDestination0+84)
DB 0
DB 0FFh,015h
DWORD (TemplateExternal0Field)-(TemplateDestination0+90)
DB 0E8h
DWORD TemplateDestination0-(TemplateDestination0+95)
DB 0E8h
DWORD TemplateExternal0-(TemplateDestination0+100)
DB 048h,087h,000h
else
DB 0A3h
DWORD TemplateDestination0+1
DB 0A3h
DWORD TemplateExternal0Field
DB 087h,005h
DWORD TemplateDestination0+1
DB 089h,005h
DWORD TemplateExternal0Field
DB 001h,005h
DWORD TemplateDestination0+1
DB 029h,005h
DWORD TemplateExternal0Field
DB 031h,005h
DWORD TemplateDestination0+1
DB 021h,005h
DWORD TemplateExternal0Field
DB 087h,025h
DWORD TemplateDestination0+1
DB 089h,025h
DWORD TemplateExternal0Field
DB 083h,01Dh
DWORD TemplateDestination0+1
DB 0
DB 0FFh,015h
DWORD TemplateExternal0Field
DB 0E8h
DWORD TemplateDestination0-(TemplateDestination0+76)
DB 0E8h
DWORD TemplateExternal0-(TemplateDestination0+81)
DB 087h,000h
endif
TemplateSource0End LABEL BYTE
TemplateSize0 EQU TemplateSource0End-TemplateSource0
TemplateDestination0 DB 256 DUP (090h)
DB 3 DUP (090h)
TemplateRun0 LABEL BYTE
ifdef X64
TRANSFERDATA TemplateCursorS0,OFFSET TemplateSource0,TemplateCursorD0,OFFSET TemplateDestination0,103
else
TRANSFERDATA TemplateCursorS0,OFFSET TemplateSource0,TemplateCursorD0,OFFSET TemplateDestination0,83
endif
TemplateStop0 LABEL BYTE
ret
TemplateDestination1 DB 256 DUP (090h)
TemplateSource1 LABEL BYTE
ifdef X64
DB 048h,0A3h
QWORD TemplateDestination1+2
DB 048h,0A3h
QWORD TemplateExternal1Field
DB 048h,087h,005h
DWORD (TemplateDestination1+2)-(TemplateDestination1+27)
DB 048h,089h,005h
DWORD (TemplateExternal1Field)-(TemplateDestination1+34)
DB 048h,001h,005h
DWORD (TemplateDestination1+2)-(TemplateDestination1+41)
DB 048h,029h,005h
DWORD (TemplateExternal1Field)-(TemplateDestination1+48)
DB 048h,031h,005h
DWORD (TemplateDestination1+2)-(TemplateDestination1+55)
DB 048h,021h,005h
DWORD (TemplateExternal1Field)-(TemplateDestination1+62)
DB 048h,087h,025h
DWORD (TemplateDestination1+2)-(TemplateDestination1+69)
DB 048h,089h,025h
DWORD (TemplateExternal1Field)-(TemplateDestination1+76)
DB 048h,083h,01Dh
DWORD (TemplateDestination1+2)-(TemplateDestination1+84)
DB 0
DB 0FFh,015h
DWORD (TemplateExternal1Field)-(TemplateDestination1+90)
DB 0E8h
DWORD TemplateDestination1-(TemplateDestination1+95)
DB 0E8h
DWORD TemplateExternal1-(TemplateDestination1+100)
DB 048h,087h,000h
else
DB 0A3h
DWORD TemplateDestination1+1
DB 0A3h
DWORD TemplateExternal1Field
DB 087h,005h
DWORD TemplateDestination1+1
DB 089h,005h
DWORD TemplateExternal1Field
DB 001h,005h
DWORD TemplateDestination1+1
DB 029h,005h
DWORD TemplateExternal1Field
DB 031h,005h
DWORD TemplateDestination1+1
DB 021h,005h
DWORD TemplateExternal1Field
DB 087h,025h
DWORD TemplateDestination1+1
DB 089h,025h
DWORD TemplateExternal1Field
DB 083h,01Dh
DWORD TemplateDestination1+1
DB 0
DB 0FFh,015h
DWORD TemplateExternal1Field
DB 0E8h
DWORD TemplateDestination1-(TemplateDestination1+76)
DB 0E8h
DWORD TemplateExternal1-(TemplateDestination1+81)
DB 087h,000h
endif
TemplateSource1End LABEL BYTE
TemplateSize1 EQU TemplateSource1End-TemplateSource1
DB 10 DUP (090h)
TemplateRun1 LABEL BYTE
ifdef X64
TRANSFERDATA TemplateCursorS1,OFFSET TemplateSource1,TemplateCursorD1,OFFSET TemplateDestination1,103
else
TRANSFERDATA TemplateCursorS1,OFFSET TemplateSource1,TemplateCursorD1,OFFSET TemplateDestination1,83
endif
TemplateStop1 LABEL BYTE
ret
TemplateSource2 LABEL BYTE
ifdef X64
DB 048h,0A3h
QWORD TemplateDestination2+2
DB 048h,0A3h
QWORD TemplateExternal2Field
DB 048h,087h,005h
DWORD (TemplateDestination2+2)-(TemplateDestination2+27)
DB 048h,089h,005h
DWORD (TemplateExternal2Field)-(TemplateDestination2+34)
DB 048h,001h,005h
DWORD (TemplateDestination2+2)-(TemplateDestination2+41)
DB 048h,029h,005h
DWORD (TemplateExternal2Field)-(TemplateDestination2+48)
DB 048h,031h,005h
DWORD (TemplateDestination2+2)-(TemplateDestination2+55)
DB 048h,021h,005h
DWORD (TemplateExternal2Field)-(TemplateDestination2+62)
DB 048h,087h,025h
DWORD (TemplateDestination2+2)-(TemplateDestination2+69)
DB 048h,089h,025h
DWORD (TemplateExternal2Field)-(TemplateDestination2+76)
DB 048h,083h,01Dh
DWORD (TemplateDestination2+2)-(TemplateDestination2+84)
DB 0
DB 0FFh,015h
DWORD (TemplateExternal2Field)-(TemplateDestination2+90)
DB 0E8h
DWORD TemplateDestination2-(TemplateDestination2+95)
DB 0E8h
DWORD TemplateExternal2-(TemplateDestination2+100)
DB 048h,087h,000h
else
DB 0A3h
DWORD TemplateDestination2+1
DB 0A3h
DWORD TemplateExternal2Field
DB 087h,005h
DWORD TemplateDestination2+1
DB 089h,005h
DWORD TemplateExternal2Field
DB 001h,005h
DWORD TemplateDestination2+1
DB 029h,005h
DWORD TemplateExternal2Field
DB 031h,005h
DWORD TemplateDestination2+1
DB 021h,005h
DWORD TemplateExternal2Field
DB 087h,025h
DWORD TemplateDestination2+1
DB 089h,025h
DWORD TemplateExternal2Field
DB 083h,01Dh
DWORD TemplateDestination2+1
DB 0
DB 0FFh,015h
DWORD TemplateExternal2Field
DB 0E8h
DWORD TemplateDestination2-(TemplateDestination2+76)
DB 0E8h
DWORD TemplateExternal2-(TemplateDestination2+81)
DB 087h,000h
endif
TemplateSource2End LABEL BYTE
TemplateSize2 EQU TemplateSource2End-TemplateSource2
TemplateDestination2 DB 256 DUP (090h)
DB 17 DUP (090h)
TemplateRun2 LABEL BYTE
ifdef X64
TRANSFERDATA TemplateCursorS2,OFFSET TemplateSource2,TemplateCursorD2,OFFSET TemplateDestination2,103
else
TRANSFERDATA TemplateCursorS2,OFFSET TemplateSource2,TemplateCursorD2,OFFSET TemplateDestination2,83
endif
TemplateStop2 LABEL BYTE
ret
TemplateDestination3 DB 256 DUP (090h)
TemplateSource3 LABEL BYTE
ifdef X64
DB 048h,0A3h
QWORD TemplateDestination3+2
DB 048h,0A3h
QWORD TemplateExternal3Field
DB 048h,087h,005h
DWORD (TemplateDestination3+2)-(TemplateDestination3+27)
DB 048h,089h,005h
DWORD (TemplateExternal3Field)-(TemplateDestination3+34)
DB 048h,001h,005h
DWORD (TemplateDestination3+2)-(TemplateDestination3+41)
DB 048h,029h,005h
DWORD (TemplateExternal3Field)-(TemplateDestination3+48)
DB 048h,031h,005h
DWORD (TemplateDestination3+2)-(TemplateDestination3+55)
DB 048h,021h,005h
DWORD (TemplateExternal3Field)-(TemplateDestination3+62)
DB 048h,087h,025h
DWORD (TemplateDestination3+2)-(TemplateDestination3+69)
DB 048h,089h,025h
DWORD (TemplateExternal3Field)-(TemplateDestination3+76)
DB 048h,083h,01Dh
DWORD (TemplateDestination3+2)-(TemplateDestination3+84)
DB 0
DB 0FFh,015h
DWORD (TemplateExternal3Field)-(TemplateDestination3+90)
DB 0E8h
DWORD TemplateDestination3-(TemplateDestination3+95)
DB 0E8h
DWORD TemplateExternal3-(TemplateDestination3+100)
DB 048h,087h,000h
else
DB 0A3h
DWORD TemplateDestination3+1
DB 0A3h
DWORD TemplateExternal3Field
DB 087h,005h
DWORD TemplateDestination3+1
DB 089h,005h
DWORD TemplateExternal3Field
DB 001h,005h
DWORD TemplateDestination3+1
DB 029h,005h
DWORD TemplateExternal3Field
DB 031h,005h
DWORD TemplateDestination3+1
DB 021h,005h
DWORD TemplateExternal3Field
DB 087h,025h
DWORD TemplateDestination3+1
DB 089h,025h
DWORD TemplateExternal3Field
DB 083h,01Dh
DWORD TemplateDestination3+1
DB 0
DB 0FFh,015h
DWORD TemplateExternal3Field
DB 0E8h
DWORD TemplateDestination3-(TemplateDestination3+76)
DB 0E8h
DWORD TemplateExternal3-(TemplateDestination3+81)
DB 087h,000h
endif
TemplateSource3End LABEL BYTE
TemplateSize3 EQU TemplateSource3End-TemplateSource3
DB 24 DUP (090h)
TemplateRun3 LABEL BYTE
ifdef X64
TRANSFERDATA TemplateCursorS3,OFFSET TemplateSource3,TemplateCursorD3,OFFSET TemplateDestination3,103
else
TRANSFERDATA TemplateCursorS3,OFFSET TemplateSource3,TemplateCursorD3,OFFSET TemplateDestination3,83
endif
TemplateStop3 LABEL BYTE
ret
END
