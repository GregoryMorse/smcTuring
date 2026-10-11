ifndef X64
.686
.model flat,C
endif
option casemap:none
include listing5_smc.inc
.data
PUBLIC TransferObservation,TransferIndexSeeds,TransferSource,TransferDestination,TransferWrongSource,TransferWrongDestination
ifdef X64
TransferObservation QWORD 18 DUP(0)
TransferTarget QWORD 0
TransferIndexSeeds QWORD 2 DUP(0)
else
TransferObservation DWORD 18 DUP(0)
TransferIndexSeeds DWORD 2 DUP(0)
endif
TransferSource BYTE 640 DUP(0)
TransferDestination BYTE 640 DUP(0)
TransferWrongSource BYTE 640 DUP(0)
TransferWrongDestination BYTE 640 DUP(0)
PUBLIC TransferFixtureCount,TransferFixtures
TransferFixtureCount DWORD 48
ifdef X64
TransferFixtures LABEL QWORD
TransferRecord0 QWORD 0,0,TransferRun0,TransferStop0,TransferCursorS0+TRANSFER_CURSOR_OFFS,TransferCursorD0+TRANSFER_CURSOR_OFFS,TransferCursorS0CopyBegin,TransferCursorS0CopyEnd
TransferRecord1 QWORD 1,1,TransferRun1,TransferStop1,TransferCursorS1+TRANSFER_CURSOR_OFFS,TransferCursorD1+TRANSFER_CURSOR_OFFS,TransferCursorS1CopyBegin,TransferCursorS1CopyEnd
TransferRecord2 QWORD 2,2,TransferRun2,TransferStop2,TransferCursorS2+TRANSFER_CURSOR_OFFS,TransferCursorD2+TRANSFER_CURSOR_OFFS,TransferCursorS2CopyBegin,TransferCursorS2CopyEnd
TransferRecord3 QWORD 3,3,TransferRun3,TransferStop3,TransferCursorS3+TRANSFER_CURSOR_OFFS,TransferCursorD3+TRANSFER_CURSOR_OFFS,TransferCursorS3CopyBegin,TransferCursorS3CopyEnd
TransferRecord4 QWORD 4,4,TransferRun4,TransferStop4,TransferCursorS4+TRANSFER_CURSOR_OFFS,TransferCursorD4+TRANSFER_CURSOR_OFFS,TransferCursorS4CopyBegin,TransferCursorS4CopyEnd
TransferRecord5 QWORD 5,5,TransferRun5,TransferStop5,TransferCursorS5+TRANSFER_CURSOR_OFFS,TransferCursorD5+TRANSFER_CURSOR_OFFS,TransferCursorS5CopyBegin,TransferCursorS5CopyEnd
TransferRecord6 QWORD 6,6,TransferRun6,TransferStop6,TransferCursorS6+TRANSFER_CURSOR_OFFS,TransferCursorD6+TRANSFER_CURSOR_OFFS,TransferCursorS6CopyBegin,TransferCursorS6CopyEnd
TransferRecord7 QWORD 7,7,TransferRun7,TransferStop7,TransferCursorS7+TRANSFER_CURSOR_OFFS,TransferCursorD7+TRANSFER_CURSOR_OFFS,TransferCursorS7CopyBegin,TransferCursorS7CopyEnd
TransferRecord8 QWORD 8,0,TransferRun8,TransferStop8,TransferCursorS8+TRANSFER_CURSOR_OFFS,TransferCursorD8+TRANSFER_CURSOR_OFFS,TransferCursorS8CopyBegin,TransferCursorS8CopyEnd
TransferRecord9 QWORD 9,1,TransferRun9,TransferStop9,TransferCursorS9+TRANSFER_CURSOR_OFFS,TransferCursorD9+TRANSFER_CURSOR_OFFS,TransferCursorS9CopyBegin,TransferCursorS9CopyEnd
TransferRecord10 QWORD 10,2,TransferRun10,TransferStop10,TransferCursorS10+TRANSFER_CURSOR_OFFS,TransferCursorD10+TRANSFER_CURSOR_OFFS,TransferCursorS10CopyBegin,TransferCursorS10CopyEnd
TransferRecord11 QWORD 11,3,TransferRun11,TransferStop11,TransferCursorS11+TRANSFER_CURSOR_OFFS,TransferCursorD11+TRANSFER_CURSOR_OFFS,TransferCursorS11CopyBegin,TransferCursorS11CopyEnd
TransferRecord12 QWORD 12,4,TransferRun12,TransferStop12,TransferCursorS12+TRANSFER_CURSOR_OFFS,TransferCursorD12+TRANSFER_CURSOR_OFFS,TransferCursorS12CopyBegin,TransferCursorS12CopyEnd
TransferRecord13 QWORD 13,5,TransferRun13,TransferStop13,TransferCursorS13+TRANSFER_CURSOR_OFFS,TransferCursorD13+TRANSFER_CURSOR_OFFS,TransferCursorS13CopyBegin,TransferCursorS13CopyEnd
TransferRecord14 QWORD 14,6,TransferRun14,TransferStop14,TransferCursorS14+TRANSFER_CURSOR_OFFS,TransferCursorD14+TRANSFER_CURSOR_OFFS,TransferCursorS14CopyBegin,TransferCursorS14CopyEnd
TransferRecord15 QWORD 15,7,TransferRun15,TransferStop15,TransferCursorS15+TRANSFER_CURSOR_OFFS,TransferCursorD15+TRANSFER_CURSOR_OFFS,TransferCursorS15CopyBegin,TransferCursorS15CopyEnd
TransferRecord16 QWORD 16,0,TransferRun16,TransferStop16,TransferCursorS16+TRANSFER_CURSOR_OFFS,TransferCursorD16+TRANSFER_CURSOR_OFFS,TransferCursorS16CopyBegin,TransferCursorS16CopyEnd
TransferRecord17 QWORD 17,1,TransferRun17,TransferStop17,TransferCursorS17+TRANSFER_CURSOR_OFFS,TransferCursorD17+TRANSFER_CURSOR_OFFS,TransferCursorS17CopyBegin,TransferCursorS17CopyEnd
TransferRecord18 QWORD 18,2,TransferRun18,TransferStop18,TransferCursorS18+TRANSFER_CURSOR_OFFS,TransferCursorD18+TRANSFER_CURSOR_OFFS,TransferCursorS18CopyBegin,TransferCursorS18CopyEnd
TransferRecord19 QWORD 19,3,TransferRun19,TransferStop19,TransferCursorS19+TRANSFER_CURSOR_OFFS,TransferCursorD19+TRANSFER_CURSOR_OFFS,TransferCursorS19CopyBegin,TransferCursorS19CopyEnd
TransferRecord20 QWORD 20,4,TransferRun20,TransferStop20,TransferCursorS20+TRANSFER_CURSOR_OFFS,TransferCursorD20+TRANSFER_CURSOR_OFFS,TransferCursorS20CopyBegin,TransferCursorS20CopyEnd
TransferRecord21 QWORD 21,5,TransferRun21,TransferStop21,TransferCursorS21+TRANSFER_CURSOR_OFFS,TransferCursorD21+TRANSFER_CURSOR_OFFS,TransferCursorS21CopyBegin,TransferCursorS21CopyEnd
TransferRecord22 QWORD 22,6,TransferRun22,TransferStop22,TransferCursorS22+TRANSFER_CURSOR_OFFS,TransferCursorD22+TRANSFER_CURSOR_OFFS,TransferCursorS22CopyBegin,TransferCursorS22CopyEnd
TransferRecord23 QWORD 23,7,TransferRun23,TransferStop23,TransferCursorS23+TRANSFER_CURSOR_OFFS,TransferCursorD23+TRANSFER_CURSOR_OFFS,TransferCursorS23CopyBegin,TransferCursorS23CopyEnd
TransferRecord24 QWORD 24,0,TransferRun24,TransferStop24,TransferCursorS24+TRANSFER_CURSOR_OFFS,TransferCursorD24+TRANSFER_CURSOR_OFFS,TransferCursorS24CopyBegin,TransferCursorS24CopyEnd
TransferRecord25 QWORD 25,1,TransferRun25,TransferStop25,TransferCursorS25+TRANSFER_CURSOR_OFFS,TransferCursorD25+TRANSFER_CURSOR_OFFS,TransferCursorS25CopyBegin,TransferCursorS25CopyEnd
TransferRecord26 QWORD 26,2,TransferRun26,TransferStop26,TransferCursorS26+TRANSFER_CURSOR_OFFS,TransferCursorD26+TRANSFER_CURSOR_OFFS,TransferCursorS26CopyBegin,TransferCursorS26CopyEnd
TransferRecord27 QWORD 27,3,TransferRun27,TransferStop27,TransferCursorS27+TRANSFER_CURSOR_OFFS,TransferCursorD27+TRANSFER_CURSOR_OFFS,TransferCursorS27CopyBegin,TransferCursorS27CopyEnd
TransferRecord28 QWORD 28,4,TransferRun28,TransferStop28,TransferCursorS28+TRANSFER_CURSOR_OFFS,TransferCursorD28+TRANSFER_CURSOR_OFFS,TransferCursorS28CopyBegin,TransferCursorS28CopyEnd
TransferRecord29 QWORD 29,5,TransferRun29,TransferStop29,TransferCursorS29+TRANSFER_CURSOR_OFFS,TransferCursorD29+TRANSFER_CURSOR_OFFS,TransferCursorS29CopyBegin,TransferCursorS29CopyEnd
TransferRecord30 QWORD 30,6,TransferRun30,TransferStop30,TransferCursorS30+TRANSFER_CURSOR_OFFS,TransferCursorD30+TRANSFER_CURSOR_OFFS,TransferCursorS30CopyBegin,TransferCursorS30CopyEnd
TransferRecord31 QWORD 31,7,TransferRun31,TransferStop31,TransferCursorS31+TRANSFER_CURSOR_OFFS,TransferCursorD31+TRANSFER_CURSOR_OFFS,TransferCursorS31CopyBegin,TransferCursorS31CopyEnd
TransferRecord32 QWORD 32,0,TransferRun32,TransferStop32,TransferCursorS32+TRANSFER_CURSOR_OFFS,TransferCursorD32+TRANSFER_CURSOR_OFFS,TransferCursorS32CopyBegin,TransferCursorS32CopyEnd
TransferRecord33 QWORD 33,1,TransferRun33,TransferStop33,TransferCursorS33+TRANSFER_CURSOR_OFFS,TransferCursorD33+TRANSFER_CURSOR_OFFS,TransferCursorS33CopyBegin,TransferCursorS33CopyEnd
TransferRecord34 QWORD 34,2,TransferRun34,TransferStop34,TransferCursorS34+TRANSFER_CURSOR_OFFS,TransferCursorD34+TRANSFER_CURSOR_OFFS,TransferCursorS34CopyBegin,TransferCursorS34CopyEnd
TransferRecord35 QWORD 35,3,TransferRun35,TransferStop35,TransferCursorS35+TRANSFER_CURSOR_OFFS,TransferCursorD35+TRANSFER_CURSOR_OFFS,TransferCursorS35CopyBegin,TransferCursorS35CopyEnd
TransferRecord63 QWORD 63,7,TransferRun63,TransferStop63,TransferCursorS63+TRANSFER_CURSOR_OFFS,TransferCursorD63+TRANSFER_CURSOR_OFFS,TransferCursorS63CopyBegin,TransferCursorS63CopyEnd
TransferRecord64 QWORD 64,0,TransferRun64,TransferStop64,TransferCursorS64+TRANSFER_CURSOR_OFFS,TransferCursorD64+TRANSFER_CURSOR_OFFS,TransferCursorS64CopyBegin,TransferCursorS64CopyEnd
TransferRecord65 QWORD 65,1,TransferRun65,TransferStop65,TransferCursorS65+TRANSFER_CURSOR_OFFS,TransferCursorD65+TRANSFER_CURSOR_OFFS,TransferCursorS65CopyBegin,TransferCursorS65CopyEnd
TransferRecord127 QWORD 127,7,TransferRun127,TransferStop127,TransferCursorS127+TRANSFER_CURSOR_OFFS,TransferCursorD127+TRANSFER_CURSOR_OFFS,TransferCursorS127CopyBegin,TransferCursorS127CopyEnd
TransferRecord128 QWORD 128,0,TransferRun128,TransferStop128,TransferCursorS128+TRANSFER_CURSOR_OFFS,TransferCursorD128+TRANSFER_CURSOR_OFFS,TransferCursorS128CopyBegin,TransferCursorS128CopyEnd
TransferRecord129 QWORD 129,1,TransferRun129,TransferStop129,TransferCursorS129+TRANSFER_CURSOR_OFFS,TransferCursorD129+TRANSFER_CURSOR_OFFS,TransferCursorS129CopyBegin,TransferCursorS129CopyEnd
TransferRecord255 QWORD 255,7,TransferRun255,TransferStop255,TransferCursorS255+TRANSFER_CURSOR_OFFS,TransferCursorD255+TRANSFER_CURSOR_OFFS,TransferCursorS255CopyBegin,TransferCursorS255CopyEnd
TransferRecord256 QWORD 256,0,TransferRun256,TransferStop256,TransferCursorS256+TRANSFER_CURSOR_OFFS,TransferCursorD256+TRANSFER_CURSOR_OFFS,TransferCursorS256CopyBegin,TransferCursorS256CopyEnd
TransferRecord257 QWORD 257,1,TransferRun257,TransferStop257,TransferCursorS257+TRANSFER_CURSOR_OFFS,TransferCursorD257+TRANSFER_CURSOR_OFFS,TransferCursorS257CopyBegin,TransferCursorS257CopyEnd
TransferRecord511 QWORD 511,7,TransferRun511,TransferStop511,TransferCursorS511+TRANSFER_CURSOR_OFFS,TransferCursorD511+TRANSFER_CURSOR_OFFS,TransferCursorS511CopyBegin,TransferCursorS511CopyEnd
TransferRecord512 QWORD 512,0,TransferRun512,TransferStop512,TransferCursorS512+TRANSFER_CURSOR_OFFS,TransferCursorD512+TRANSFER_CURSOR_OFFS,TransferCursorS512CopyBegin,TransferCursorS512CopyEnd
TransferRecord513 QWORD 513,1,TransferRun513,TransferStop513,TransferCursorS513+TRANSFER_CURSOR_OFFS,TransferCursorD513+TRANSFER_CURSOR_OFFS,TransferCursorS513CopyBegin,TransferCursorS513CopyEnd
else
TransferFixtures LABEL DWORD
TransferRecord0 DWORD 0,0,TransferRun0,TransferStop0,TransferCursorS0+TRANSFER_CURSOR_OFFS,TransferCursorD0+TRANSFER_CURSOR_OFFS,TransferCursorS0CopyBegin,TransferCursorS0CopyEnd
TransferRecord1 DWORD 1,1,TransferRun1,TransferStop1,TransferCursorS1+TRANSFER_CURSOR_OFFS,TransferCursorD1+TRANSFER_CURSOR_OFFS,TransferCursorS1CopyBegin,TransferCursorS1CopyEnd
TransferRecord2 DWORD 2,2,TransferRun2,TransferStop2,TransferCursorS2+TRANSFER_CURSOR_OFFS,TransferCursorD2+TRANSFER_CURSOR_OFFS,TransferCursorS2CopyBegin,TransferCursorS2CopyEnd
TransferRecord3 DWORD 3,3,TransferRun3,TransferStop3,TransferCursorS3+TRANSFER_CURSOR_OFFS,TransferCursorD3+TRANSFER_CURSOR_OFFS,TransferCursorS3CopyBegin,TransferCursorS3CopyEnd
TransferRecord4 DWORD 4,4,TransferRun4,TransferStop4,TransferCursorS4+TRANSFER_CURSOR_OFFS,TransferCursorD4+TRANSFER_CURSOR_OFFS,TransferCursorS4CopyBegin,TransferCursorS4CopyEnd
TransferRecord5 DWORD 5,5,TransferRun5,TransferStop5,TransferCursorS5+TRANSFER_CURSOR_OFFS,TransferCursorD5+TRANSFER_CURSOR_OFFS,TransferCursorS5CopyBegin,TransferCursorS5CopyEnd
TransferRecord6 DWORD 6,6,TransferRun6,TransferStop6,TransferCursorS6+TRANSFER_CURSOR_OFFS,TransferCursorD6+TRANSFER_CURSOR_OFFS,TransferCursorS6CopyBegin,TransferCursorS6CopyEnd
TransferRecord7 DWORD 7,7,TransferRun7,TransferStop7,TransferCursorS7+TRANSFER_CURSOR_OFFS,TransferCursorD7+TRANSFER_CURSOR_OFFS,TransferCursorS7CopyBegin,TransferCursorS7CopyEnd
TransferRecord8 DWORD 8,0,TransferRun8,TransferStop8,TransferCursorS8+TRANSFER_CURSOR_OFFS,TransferCursorD8+TRANSFER_CURSOR_OFFS,TransferCursorS8CopyBegin,TransferCursorS8CopyEnd
TransferRecord9 DWORD 9,1,TransferRun9,TransferStop9,TransferCursorS9+TRANSFER_CURSOR_OFFS,TransferCursorD9+TRANSFER_CURSOR_OFFS,TransferCursorS9CopyBegin,TransferCursorS9CopyEnd
TransferRecord10 DWORD 10,2,TransferRun10,TransferStop10,TransferCursorS10+TRANSFER_CURSOR_OFFS,TransferCursorD10+TRANSFER_CURSOR_OFFS,TransferCursorS10CopyBegin,TransferCursorS10CopyEnd
TransferRecord11 DWORD 11,3,TransferRun11,TransferStop11,TransferCursorS11+TRANSFER_CURSOR_OFFS,TransferCursorD11+TRANSFER_CURSOR_OFFS,TransferCursorS11CopyBegin,TransferCursorS11CopyEnd
TransferRecord12 DWORD 12,4,TransferRun12,TransferStop12,TransferCursorS12+TRANSFER_CURSOR_OFFS,TransferCursorD12+TRANSFER_CURSOR_OFFS,TransferCursorS12CopyBegin,TransferCursorS12CopyEnd
TransferRecord13 DWORD 13,5,TransferRun13,TransferStop13,TransferCursorS13+TRANSFER_CURSOR_OFFS,TransferCursorD13+TRANSFER_CURSOR_OFFS,TransferCursorS13CopyBegin,TransferCursorS13CopyEnd
TransferRecord14 DWORD 14,6,TransferRun14,TransferStop14,TransferCursorS14+TRANSFER_CURSOR_OFFS,TransferCursorD14+TRANSFER_CURSOR_OFFS,TransferCursorS14CopyBegin,TransferCursorS14CopyEnd
TransferRecord15 DWORD 15,7,TransferRun15,TransferStop15,TransferCursorS15+TRANSFER_CURSOR_OFFS,TransferCursorD15+TRANSFER_CURSOR_OFFS,TransferCursorS15CopyBegin,TransferCursorS15CopyEnd
TransferRecord16 DWORD 16,0,TransferRun16,TransferStop16,TransferCursorS16+TRANSFER_CURSOR_OFFS,TransferCursorD16+TRANSFER_CURSOR_OFFS,TransferCursorS16CopyBegin,TransferCursorS16CopyEnd
TransferRecord17 DWORD 17,1,TransferRun17,TransferStop17,TransferCursorS17+TRANSFER_CURSOR_OFFS,TransferCursorD17+TRANSFER_CURSOR_OFFS,TransferCursorS17CopyBegin,TransferCursorS17CopyEnd
TransferRecord18 DWORD 18,2,TransferRun18,TransferStop18,TransferCursorS18+TRANSFER_CURSOR_OFFS,TransferCursorD18+TRANSFER_CURSOR_OFFS,TransferCursorS18CopyBegin,TransferCursorS18CopyEnd
TransferRecord19 DWORD 19,3,TransferRun19,TransferStop19,TransferCursorS19+TRANSFER_CURSOR_OFFS,TransferCursorD19+TRANSFER_CURSOR_OFFS,TransferCursorS19CopyBegin,TransferCursorS19CopyEnd
TransferRecord20 DWORD 20,4,TransferRun20,TransferStop20,TransferCursorS20+TRANSFER_CURSOR_OFFS,TransferCursorD20+TRANSFER_CURSOR_OFFS,TransferCursorS20CopyBegin,TransferCursorS20CopyEnd
TransferRecord21 DWORD 21,5,TransferRun21,TransferStop21,TransferCursorS21+TRANSFER_CURSOR_OFFS,TransferCursorD21+TRANSFER_CURSOR_OFFS,TransferCursorS21CopyBegin,TransferCursorS21CopyEnd
TransferRecord22 DWORD 22,6,TransferRun22,TransferStop22,TransferCursorS22+TRANSFER_CURSOR_OFFS,TransferCursorD22+TRANSFER_CURSOR_OFFS,TransferCursorS22CopyBegin,TransferCursorS22CopyEnd
TransferRecord23 DWORD 23,7,TransferRun23,TransferStop23,TransferCursorS23+TRANSFER_CURSOR_OFFS,TransferCursorD23+TRANSFER_CURSOR_OFFS,TransferCursorS23CopyBegin,TransferCursorS23CopyEnd
TransferRecord24 DWORD 24,0,TransferRun24,TransferStop24,TransferCursorS24+TRANSFER_CURSOR_OFFS,TransferCursorD24+TRANSFER_CURSOR_OFFS,TransferCursorS24CopyBegin,TransferCursorS24CopyEnd
TransferRecord25 DWORD 25,1,TransferRun25,TransferStop25,TransferCursorS25+TRANSFER_CURSOR_OFFS,TransferCursorD25+TRANSFER_CURSOR_OFFS,TransferCursorS25CopyBegin,TransferCursorS25CopyEnd
TransferRecord26 DWORD 26,2,TransferRun26,TransferStop26,TransferCursorS26+TRANSFER_CURSOR_OFFS,TransferCursorD26+TRANSFER_CURSOR_OFFS,TransferCursorS26CopyBegin,TransferCursorS26CopyEnd
TransferRecord27 DWORD 27,3,TransferRun27,TransferStop27,TransferCursorS27+TRANSFER_CURSOR_OFFS,TransferCursorD27+TRANSFER_CURSOR_OFFS,TransferCursorS27CopyBegin,TransferCursorS27CopyEnd
TransferRecord28 DWORD 28,4,TransferRun28,TransferStop28,TransferCursorS28+TRANSFER_CURSOR_OFFS,TransferCursorD28+TRANSFER_CURSOR_OFFS,TransferCursorS28CopyBegin,TransferCursorS28CopyEnd
TransferRecord29 DWORD 29,5,TransferRun29,TransferStop29,TransferCursorS29+TRANSFER_CURSOR_OFFS,TransferCursorD29+TRANSFER_CURSOR_OFFS,TransferCursorS29CopyBegin,TransferCursorS29CopyEnd
TransferRecord30 DWORD 30,6,TransferRun30,TransferStop30,TransferCursorS30+TRANSFER_CURSOR_OFFS,TransferCursorD30+TRANSFER_CURSOR_OFFS,TransferCursorS30CopyBegin,TransferCursorS30CopyEnd
TransferRecord31 DWORD 31,7,TransferRun31,TransferStop31,TransferCursorS31+TRANSFER_CURSOR_OFFS,TransferCursorD31+TRANSFER_CURSOR_OFFS,TransferCursorS31CopyBegin,TransferCursorS31CopyEnd
TransferRecord32 DWORD 32,0,TransferRun32,TransferStop32,TransferCursorS32+TRANSFER_CURSOR_OFFS,TransferCursorD32+TRANSFER_CURSOR_OFFS,TransferCursorS32CopyBegin,TransferCursorS32CopyEnd
TransferRecord33 DWORD 33,1,TransferRun33,TransferStop33,TransferCursorS33+TRANSFER_CURSOR_OFFS,TransferCursorD33+TRANSFER_CURSOR_OFFS,TransferCursorS33CopyBegin,TransferCursorS33CopyEnd
TransferRecord34 DWORD 34,2,TransferRun34,TransferStop34,TransferCursorS34+TRANSFER_CURSOR_OFFS,TransferCursorD34+TRANSFER_CURSOR_OFFS,TransferCursorS34CopyBegin,TransferCursorS34CopyEnd
TransferRecord35 DWORD 35,3,TransferRun35,TransferStop35,TransferCursorS35+TRANSFER_CURSOR_OFFS,TransferCursorD35+TRANSFER_CURSOR_OFFS,TransferCursorS35CopyBegin,TransferCursorS35CopyEnd
TransferRecord63 DWORD 63,7,TransferRun63,TransferStop63,TransferCursorS63+TRANSFER_CURSOR_OFFS,TransferCursorD63+TRANSFER_CURSOR_OFFS,TransferCursorS63CopyBegin,TransferCursorS63CopyEnd
TransferRecord64 DWORD 64,0,TransferRun64,TransferStop64,TransferCursorS64+TRANSFER_CURSOR_OFFS,TransferCursorD64+TRANSFER_CURSOR_OFFS,TransferCursorS64CopyBegin,TransferCursorS64CopyEnd
TransferRecord65 DWORD 65,1,TransferRun65,TransferStop65,TransferCursorS65+TRANSFER_CURSOR_OFFS,TransferCursorD65+TRANSFER_CURSOR_OFFS,TransferCursorS65CopyBegin,TransferCursorS65CopyEnd
TransferRecord127 DWORD 127,7,TransferRun127,TransferStop127,TransferCursorS127+TRANSFER_CURSOR_OFFS,TransferCursorD127+TRANSFER_CURSOR_OFFS,TransferCursorS127CopyBegin,TransferCursorS127CopyEnd
TransferRecord128 DWORD 128,0,TransferRun128,TransferStop128,TransferCursorS128+TRANSFER_CURSOR_OFFS,TransferCursorD128+TRANSFER_CURSOR_OFFS,TransferCursorS128CopyBegin,TransferCursorS128CopyEnd
TransferRecord129 DWORD 129,1,TransferRun129,TransferStop129,TransferCursorS129+TRANSFER_CURSOR_OFFS,TransferCursorD129+TRANSFER_CURSOR_OFFS,TransferCursorS129CopyBegin,TransferCursorS129CopyEnd
TransferRecord255 DWORD 255,7,TransferRun255,TransferStop255,TransferCursorS255+TRANSFER_CURSOR_OFFS,TransferCursorD255+TRANSFER_CURSOR_OFFS,TransferCursorS255CopyBegin,TransferCursorS255CopyEnd
TransferRecord256 DWORD 256,0,TransferRun256,TransferStop256,TransferCursorS256+TRANSFER_CURSOR_OFFS,TransferCursorD256+TRANSFER_CURSOR_OFFS,TransferCursorS256CopyBegin,TransferCursorS256CopyEnd
TransferRecord257 DWORD 257,1,TransferRun257,TransferStop257,TransferCursorS257+TRANSFER_CURSOR_OFFS,TransferCursorD257+TRANSFER_CURSOR_OFFS,TransferCursorS257CopyBegin,TransferCursorS257CopyEnd
TransferRecord511 DWORD 511,7,TransferRun511,TransferStop511,TransferCursorS511+TRANSFER_CURSOR_OFFS,TransferCursorD511+TRANSFER_CURSOR_OFFS,TransferCursorS511CopyBegin,TransferCursorS511CopyEnd
TransferRecord512 DWORD 512,0,TransferRun512,TransferStop512,TransferCursorS512+TRANSFER_CURSOR_OFFS,TransferCursorD512+TRANSFER_CURSOR_OFFS,TransferCursorS512CopyBegin,TransferCursorS512CopyEnd
TransferRecord513 DWORD 513,1,TransferRun513,TransferStop513,TransferCursorS513+TRANSFER_CURSOR_OFFS,TransferCursorD513+TRANSFER_CURSOR_OFFS,TransferCursorS513CopyBegin,TransferCursorS513CopyEnd
endif
.code
PUBLIC TransferBegin,TransferEnd,TransferPrinted,TransferPrintedStop
TransferBegin LABEL BYTE
; Typed literal Listing 5 baseline; initializer expressions are unchanged.
TransferPrinted LABEL BYTE
    DEFDATA_TRANSFER TransferPrintedS,OFFSET TransferSource
    xchg TRANSFER_SI,SMC_WORD PTR [OFFSET TransferSource]
    DEFDATA_TRANSFER TransferPrintedD,OFFSET TransferDestination
    xchg TRANSFER_DI,SMC_WORD PTR [OFFSET TransferDestination]
    MOVSMACRO 16
    xchg TRANSFER_SI,SMC_WORD PTR [OFFSET TransferSource]
    sub SMC_WORD PTR [OFFSET TransferSource],16
    xchg TRANSFER_DI,SMC_WORD PTR [OFFSET TransferDestination]
    sub SMC_WORD PTR [OFFSET TransferDestination],16
TransferPrintedStop LABEL BYTE
    ret
PUBLIC TransferRun0,TransferStop0
TransferRun0 LABEL BYTE
    TRANSFERDATA TransferCursorS0,OFFSET TransferSource+0,TransferCursorD0,OFFSET TransferDestination+0,0
TransferStop0 LABEL BYTE
    ret
PUBLIC TransferRun1,TransferStop1
TransferRun1 LABEL BYTE
    TRANSFERDATA TransferCursorS1,OFFSET TransferSource+1,TransferCursorD1,OFFSET TransferDestination+1,1
TransferStop1 LABEL BYTE
    ret
PUBLIC TransferRun2,TransferStop2
TransferRun2 LABEL BYTE
    TRANSFERDATA TransferCursorS2,OFFSET TransferSource+2,TransferCursorD2,OFFSET TransferDestination+2,2
TransferStop2 LABEL BYTE
    ret
PUBLIC TransferRun3,TransferStop3
TransferRun3 LABEL BYTE
    TRANSFERDATA TransferCursorS3,OFFSET TransferSource+3,TransferCursorD3,OFFSET TransferDestination+3,3
TransferStop3 LABEL BYTE
    ret
PUBLIC TransferRun4,TransferStop4
TransferRun4 LABEL BYTE
    TRANSFERDATA TransferCursorS4,OFFSET TransferSource+4,TransferCursorD4,OFFSET TransferDestination+4,4
TransferStop4 LABEL BYTE
    ret
PUBLIC TransferRun5,TransferStop5
TransferRun5 LABEL BYTE
    TRANSFERDATA TransferCursorS5,OFFSET TransferSource+5,TransferCursorD5,OFFSET TransferDestination+5,5
TransferStop5 LABEL BYTE
    ret
PUBLIC TransferRun6,TransferStop6
TransferRun6 LABEL BYTE
    TRANSFERDATA TransferCursorS6,OFFSET TransferSource+6,TransferCursorD6,OFFSET TransferDestination+6,6
TransferStop6 LABEL BYTE
    ret
PUBLIC TransferRun7,TransferStop7
TransferRun7 LABEL BYTE
    TRANSFERDATA TransferCursorS7,OFFSET TransferSource+7,TransferCursorD7,OFFSET TransferDestination+7,7
TransferStop7 LABEL BYTE
    ret
PUBLIC TransferRun8,TransferStop8
TransferRun8 LABEL BYTE
    TRANSFERDATA TransferCursorS8,OFFSET TransferSource+0,TransferCursorD8,OFFSET TransferDestination+0,8
TransferStop8 LABEL BYTE
    ret
PUBLIC TransferRun9,TransferStop9
TransferRun9 LABEL BYTE
    TRANSFERDATA TransferCursorS9,OFFSET TransferSource+1,TransferCursorD9,OFFSET TransferDestination+1,9
TransferStop9 LABEL BYTE
    ret
PUBLIC TransferRun10,TransferStop10
TransferRun10 LABEL BYTE
    TRANSFERDATA TransferCursorS10,OFFSET TransferSource+2,TransferCursorD10,OFFSET TransferDestination+2,10
TransferStop10 LABEL BYTE
    ret
PUBLIC TransferRun11,TransferStop11
TransferRun11 LABEL BYTE
    TRANSFERDATA TransferCursorS11,OFFSET TransferSource+3,TransferCursorD11,OFFSET TransferDestination+3,11
TransferStop11 LABEL BYTE
    ret
PUBLIC TransferRun12,TransferStop12
TransferRun12 LABEL BYTE
    TRANSFERDATA TransferCursorS12,OFFSET TransferSource+4,TransferCursorD12,OFFSET TransferDestination+4,12
TransferStop12 LABEL BYTE
    ret
PUBLIC TransferRun13,TransferStop13
TransferRun13 LABEL BYTE
    TRANSFERDATA TransferCursorS13,OFFSET TransferSource+5,TransferCursorD13,OFFSET TransferDestination+5,13
TransferStop13 LABEL BYTE
    ret
PUBLIC TransferRun14,TransferStop14
TransferRun14 LABEL BYTE
    TRANSFERDATA TransferCursorS14,OFFSET TransferSource+6,TransferCursorD14,OFFSET TransferDestination+6,14
TransferStop14 LABEL BYTE
    ret
PUBLIC TransferRun15,TransferStop15
TransferRun15 LABEL BYTE
    TRANSFERDATA TransferCursorS15,OFFSET TransferSource+7,TransferCursorD15,OFFSET TransferDestination+7,15
TransferStop15 LABEL BYTE
    ret
PUBLIC TransferRun16,TransferStop16
TransferRun16 LABEL BYTE
    TRANSFERDATA TransferCursorS16,OFFSET TransferSource+0,TransferCursorD16,OFFSET TransferDestination+0,16
TransferStop16 LABEL BYTE
    ret
PUBLIC TransferRun17,TransferStop17
TransferRun17 LABEL BYTE
    TRANSFERDATA TransferCursorS17,OFFSET TransferSource+1,TransferCursorD17,OFFSET TransferDestination+1,17
TransferStop17 LABEL BYTE
    ret
PUBLIC TransferRun18,TransferStop18
TransferRun18 LABEL BYTE
    TRANSFERDATA TransferCursorS18,OFFSET TransferSource+2,TransferCursorD18,OFFSET TransferDestination+2,18
TransferStop18 LABEL BYTE
    ret
PUBLIC TransferRun19,TransferStop19
TransferRun19 LABEL BYTE
    TRANSFERDATA TransferCursorS19,OFFSET TransferSource+3,TransferCursorD19,OFFSET TransferDestination+3,19
TransferStop19 LABEL BYTE
    ret
PUBLIC TransferRun20,TransferStop20
TransferRun20 LABEL BYTE
    TRANSFERDATA TransferCursorS20,OFFSET TransferSource+4,TransferCursorD20,OFFSET TransferDestination+4,20
TransferStop20 LABEL BYTE
    ret
PUBLIC TransferRun21,TransferStop21
TransferRun21 LABEL BYTE
    TRANSFERDATA TransferCursorS21,OFFSET TransferSource+5,TransferCursorD21,OFFSET TransferDestination+5,21
TransferStop21 LABEL BYTE
    ret
PUBLIC TransferRun22,TransferStop22
TransferRun22 LABEL BYTE
    TRANSFERDATA TransferCursorS22,OFFSET TransferSource+6,TransferCursorD22,OFFSET TransferDestination+6,22
TransferStop22 LABEL BYTE
    ret
PUBLIC TransferRun23,TransferStop23
TransferRun23 LABEL BYTE
    TRANSFERDATA TransferCursorS23,OFFSET TransferSource+7,TransferCursorD23,OFFSET TransferDestination+7,23
TransferStop23 LABEL BYTE
    ret
PUBLIC TransferRun24,TransferStop24
TransferRun24 LABEL BYTE
    TRANSFERDATA TransferCursorS24,OFFSET TransferSource+0,TransferCursorD24,OFFSET TransferDestination+0,24
TransferStop24 LABEL BYTE
    ret
PUBLIC TransferRun25,TransferStop25
TransferRun25 LABEL BYTE
    TRANSFERDATA TransferCursorS25,OFFSET TransferSource+1,TransferCursorD25,OFFSET TransferDestination+1,25
TransferStop25 LABEL BYTE
    ret
PUBLIC TransferRun26,TransferStop26
TransferRun26 LABEL BYTE
    TRANSFERDATA TransferCursorS26,OFFSET TransferSource+2,TransferCursorD26,OFFSET TransferDestination+2,26
TransferStop26 LABEL BYTE
    ret
PUBLIC TransferRun27,TransferStop27
TransferRun27 LABEL BYTE
    TRANSFERDATA TransferCursorS27,OFFSET TransferSource+3,TransferCursorD27,OFFSET TransferDestination+3,27
TransferStop27 LABEL BYTE
    ret
PUBLIC TransferRun28,TransferStop28
TransferRun28 LABEL BYTE
    TRANSFERDATA TransferCursorS28,OFFSET TransferSource+4,TransferCursorD28,OFFSET TransferDestination+4,28
TransferStop28 LABEL BYTE
    ret
PUBLIC TransferRun29,TransferStop29
TransferRun29 LABEL BYTE
    TRANSFERDATA TransferCursorS29,OFFSET TransferSource+5,TransferCursorD29,OFFSET TransferDestination+5,29
TransferStop29 LABEL BYTE
    ret
PUBLIC TransferRun30,TransferStop30
TransferRun30 LABEL BYTE
    TRANSFERDATA TransferCursorS30,OFFSET TransferSource+6,TransferCursorD30,OFFSET TransferDestination+6,30
TransferStop30 LABEL BYTE
    ret
PUBLIC TransferRun31,TransferStop31
TransferRun31 LABEL BYTE
    TRANSFERDATA TransferCursorS31,OFFSET TransferSource+7,TransferCursorD31,OFFSET TransferDestination+7,31
TransferStop31 LABEL BYTE
    ret
PUBLIC TransferRun32,TransferStop32
TransferRun32 LABEL BYTE
    TRANSFERDATA TransferCursorS32,OFFSET TransferSource+0,TransferCursorD32,OFFSET TransferDestination+0,32
TransferStop32 LABEL BYTE
    ret
PUBLIC TransferRun33,TransferStop33
TransferRun33 LABEL BYTE
    TRANSFERDATA TransferCursorS33,OFFSET TransferSource+1,TransferCursorD33,OFFSET TransferDestination+1,33
TransferStop33 LABEL BYTE
    ret
PUBLIC TransferRun34,TransferStop34
TransferRun34 LABEL BYTE
    TRANSFERDATA TransferCursorS34,OFFSET TransferSource+2,TransferCursorD34,OFFSET TransferDestination+2,34
TransferStop34 LABEL BYTE
    ret
PUBLIC TransferRun35,TransferStop35
TransferRun35 LABEL BYTE
    TRANSFERDATA TransferCursorS35,OFFSET TransferSource+3,TransferCursorD35,OFFSET TransferDestination+3,35
TransferStop35 LABEL BYTE
    ret
PUBLIC TransferRun63,TransferStop63
TransferRun63 LABEL BYTE
    TRANSFERDATA TransferCursorS63,OFFSET TransferSource+7,TransferCursorD63,OFFSET TransferDestination+7,63
TransferStop63 LABEL BYTE
    ret
PUBLIC TransferRun64,TransferStop64
TransferRun64 LABEL BYTE
    TRANSFERDATA TransferCursorS64,OFFSET TransferSource+0,TransferCursorD64,OFFSET TransferDestination+0,64
TransferStop64 LABEL BYTE
    ret
PUBLIC TransferRun65,TransferStop65
TransferRun65 LABEL BYTE
    TRANSFERDATA TransferCursorS65,OFFSET TransferSource+1,TransferCursorD65,OFFSET TransferDestination+1,65
TransferStop65 LABEL BYTE
    ret
PUBLIC TransferRun127,TransferStop127
TransferRun127 LABEL BYTE
    TRANSFERDATA TransferCursorS127,OFFSET TransferSource+7,TransferCursorD127,OFFSET TransferDestination+7,127
TransferStop127 LABEL BYTE
    ret
PUBLIC TransferRun128,TransferStop128
TransferRun128 LABEL BYTE
    TRANSFERDATA TransferCursorS128,OFFSET TransferSource+0,TransferCursorD128,OFFSET TransferDestination+0,128
TransferStop128 LABEL BYTE
    ret
PUBLIC TransferRun129,TransferStop129
TransferRun129 LABEL BYTE
    TRANSFERDATA TransferCursorS129,OFFSET TransferSource+1,TransferCursorD129,OFFSET TransferDestination+1,129
TransferStop129 LABEL BYTE
    ret
PUBLIC TransferRun255,TransferStop255
TransferRun255 LABEL BYTE
    TRANSFERDATA TransferCursorS255,OFFSET TransferSource+7,TransferCursorD255,OFFSET TransferDestination+7,255
TransferStop255 LABEL BYTE
    ret
PUBLIC TransferRun256,TransferStop256
TransferRun256 LABEL BYTE
    TRANSFERDATA TransferCursorS256,OFFSET TransferSource+0,TransferCursorD256,OFFSET TransferDestination+0,256
TransferStop256 LABEL BYTE
    ret
PUBLIC TransferRun257,TransferStop257
TransferRun257 LABEL BYTE
    TRANSFERDATA TransferCursorS257,OFFSET TransferSource+1,TransferCursorD257,OFFSET TransferDestination+1,257
TransferStop257 LABEL BYTE
    ret
PUBLIC TransferRun511,TransferStop511
TransferRun511 LABEL BYTE
    TRANSFERDATA TransferCursorS511,OFFSET TransferSource+7,TransferCursorD511,OFFSET TransferDestination+7,511
TransferStop511 LABEL BYTE
    ret
PUBLIC TransferRun512,TransferStop512
TransferRun512 LABEL BYTE
    TRANSFERDATA TransferCursorS512,OFFSET TransferSource+0,TransferCursorD512,OFFSET TransferDestination+0,512
TransferStop512 LABEL BYTE
    ret
PUBLIC TransferRun513,TransferStop513
TransferRun513 LABEL BYTE
    TRANSFERDATA TransferCursorS513,OFFSET TransferSource+1,TransferCursorD513,OFFSET TransferDestination+1,513
TransferStop513 LABEL BYTE
    ret
TransferEnd LABEL BYTE
PUBLIC TransferInvoke
TransferInvoke PROC
ifdef X64
    push rbx
    push rsi
    push rdi
    push rbp
    push r12
    push r13
    push r14
    push r15
    sub rsp,40
    mov [TransferTarget],rcx
    mov rax,rdx
    mov [TransferObservation+136],rsp
    bt r8,0
    mov rbx,013579bdfh
    mov rcx,02468ace0h
    mov rdx,0badc0deh
    mov rsi,[TransferIndexSeeds]
    mov rdi,[TransferIndexSeeds+8]
    mov rbp,076543210h
    mov r8,010203040h
    mov r9,050607080h
    mov r10,090a0b0c0h
    mov r11,0d0e0f001h
    mov r12,023456789h
    mov r13,0abcdef01h
    mov r14,031415926h
    mov r15,027182818h
    cld
    call QWORD PTR [TransferTarget]
    mov [TransferObservation],rax
    mov [TransferObservation+8],rsp
    mov [TransferObservation+16],rbx
    mov [TransferObservation+24],rcx
    mov [TransferObservation+32],rdx
    mov [TransferObservation+40],rsi
    mov [TransferObservation+48],rdi
    mov [TransferObservation+56],rbp
    mov [TransferObservation+64],r8
    mov [TransferObservation+72],r9
    mov [TransferObservation+80],r10
    mov [TransferObservation+88],r11
    mov [TransferObservation+96],r12
    mov [TransferObservation+104],r13
    mov [TransferObservation+112],r14
    mov [TransferObservation+120],r15
    pushfq
    pop QWORD PTR [TransferObservation+128]
    add rsp,40
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rdi
    pop rsi
    pop rbx
else
    push ebx
    push esi
    push edi
    push ebp
    mov eax,[esp+24]
    mov edx,[esp+28]
    mov [TransferObservation+68],esp
    bt edx,0
    mov ebx,013579bdfh
    mov ecx,02468ace0h
    mov edx,0badc0deh
    mov esi,[TransferIndexSeeds]
    mov edi,[TransferIndexSeeds+4]
    mov ebp,076543210h
    cld
    call DWORD PTR [esp+20]
    mov [TransferObservation],eax
    mov [TransferObservation+4],esp
    mov [TransferObservation+8],ebx
    mov [TransferObservation+12],ecx
    mov [TransferObservation+16],edx
    mov [TransferObservation+20],esi
    mov [TransferObservation+24],edi
    mov [TransferObservation+28],ebp
    pushfd
    pop DWORD PTR [TransferObservation+64]
    pop ebp
    pop edi
    pop esi
    pop ebx
endif
    ret
TransferInvoke ENDP
END
