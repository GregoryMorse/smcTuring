"""Exact full-width cursor exchanges around the printed DWORD tape XOR."""
from pathlib import Path
from generate_dword_owner import generate as owner_generate
ROOT=Path(__file__).resolve().parents[1]
def generate(folder,arch):
 folder.mkdir(parents=True,exist_ok=True);bootstrap=folder/'bootstrap'
 registers=owner_generate(bootstrap,arch)
 text=(bootstrap/'owner.asm').read_text(encoding='utf-8').replace('Owner','Cursor')
 text=text.replace('include dword_owner_smc.inc','include pure_smc.inc\ninclude dword_owner_smc.inc')
 block="""CursorMarker LABEL BYTE
    xchg SMC_ACC,SMC_WORD PTR [CursorPointer]
CursorXor LABEL BYTE
    xor DWORD PTR [SMC_ACC+6],080000000h
    xchg SMC_ACC,SMC_WORD PTR [CursorPointer]"""
 text=text.replace('    SMC_DEFDATA32 CursorMarker,0',block)
 owners="""PUBLIC CursorOwner,CursorPointer,CursorOwnerEnd,CursorTape,CursorTapeEnd,CursorXor
CursorOwner LABEL BYTE
    MOFFSMOV CursorPointer,0
CursorOwnerEnd LABEL BYTE
    SMC_DEFDATA32 CursorTape,0
CursorTapeEnd LABEL BYTE
END"""
 text=text.rsplit('END',1)[0]+owners+'\n'
 (folder/'cursor.asm').write_text(text,encoding='utf-8')
 header=(bootstrap/'owner.hpp').read_text(encoding='utf-8').replace('Owner','Cursor')
 header+='extern "C" { extern unsigned char CursorOwner[],CursorPointer[],CursorOwnerEnd[],CursorTape[],CursorTapeEnd[],CursorXor[]; }\n'
 (folder/'cursor.hpp').write_text(header,encoding='utf-8')
 return registers
