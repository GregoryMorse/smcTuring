"""Literal Listing 8 XOR/AND/XCHG/XOR/XCHG, with force-wide immediates."""
from pathlib import Path
from generate_cursor import generate as cursor_generate
ROOT=Path(__file__).resolve().parents[1]
def generate(folder,arch):
 folder.mkdir(parents=True,exist_ok=True);bootstrap=folder/'bootstrap'
 registers=cursor_generate(bootstrap,arch)
 text=(bootstrap/'cursor.asm').read_text(encoding='utf-8').replace('Cursor','Update')
 text=text.replace('UpdateMarker LABEL BYTE\n',
 """UpdateMarker LABEL BYTE
UpdateNew LABEL BYTE
    xor DWORD PTR [UpdateXor+3],080000000h
UpdateMask LABEL BYTE
    and DWORD PTR [UpdateXor+3],080000000h
UpdateBody LABEL BYTE
""")
 text=text.replace('PUBLIC UpdateOwner,','PUBLIC UpdateNew,UpdateMask,UpdateBody,UpdateOwner,')
 (folder/'update.asm').write_text(text,encoding='utf-8')
 header=(bootstrap/'cursor.hpp').read_text(encoding='utf-8').replace('Cursor','Update')
 header+='extern "C" { extern unsigned char UpdateNew[],UpdateMask[],UpdateBody[]; }\n'
 (folder/'update.hpp').write_text(header,encoding='utf-8')
 return registers
