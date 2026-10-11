"""Literal DWORD comparison, using the existing scalar owner and host capture."""
from pathlib import Path
from generate_dword_owner import generate as owner_generate
ROOT=Path(__file__).resolve().parents[1]

def generate(folder,arch):
 folder.mkdir(parents=True,exist_ok=True);bootstrap=folder/'bootstrap';registers=owner_generate(bootstrap,arch)
 text=(bootstrap/'owner.asm').read_text(encoding='utf-8').replace('Owner','Compare')
 block="""CompareMarker LABEL BYTE
    mov DWORD PTR [CompareMask+6],0
    sub DWORD PTR [CompareScalar+6],080000000h
    neg DWORD PTR [CompareScalar+6]
    sbb DWORD PTR [CompareMask+6],0
    not DWORD PTR [CompareMask+6]"""
 text=text.replace('    SMC_DEFDATA32 CompareMarker,0',block)
 owners="""PUBLIC CompareScalar,CompareScalarEnd,CompareMask,CompareMaskEnd
    SMC_DEFDATA32 CompareScalar,0
CompareScalarEnd LABEL BYTE
CompareMask LABEL BYTE
    and DWORD PTR [CompareMask+6],080000000h
CompareMaskEnd LABEL BYTE
END"""
 text=text.rsplit('END',1)[0]+owners+'\n'
 (folder/'comparison.asm').write_text(text,encoding='utf-8')
 header=(bootstrap/'owner.hpp').read_text(encoding='utf-8').replace('Owner','Compare')
 header+='extern "C" { extern unsigned char CompareScalar[],CompareScalarEnd[],CompareMask[],CompareMaskEnd[]; }\n'
 (folder/'comparison.hpp').write_text(header,encoding='utf-8')
 return registers
