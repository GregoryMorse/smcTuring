"""Generate typed published/corrected terminal fixtures; host lies outside purity."""
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def generate(folder,architecture):
    folder.mkdir(parents=True,exist_ok=True)
    wide=architecture=="x64"
    registers=["rax","rsp","rbx","rcx","rdx","rsi","rdi","rbp","r8","r9","r10","r11","r12","r13","r14","r15"] if wide else ["eax","esp","ebx","ecx","edx","esi","edi","ebp"]
    unit=8 if wide else 4
    constants={reg:0x12340000+index*0x01010101 for index,reg in enumerate(registers) if index>1}
    if wide:constants={reg:value+0x7654321000000000 for reg,value in constants.items()}
    saved=["rbx","rbp","rsi","rdi","r12","r13","r14","r15"] if wide else ["ebx","ebp","esi","edi"]
    acc,sp=registers[:2]
    pushf,popf=("pushfq","pop QWORD PTR") if wide else ("pushfd","pop DWORD PTR")
    lines=["option casemap:none"]
    if not wide:lines=[".386",".model flat,C"]+lines
    lines += ["include terminal_smc.inc",".data","PUBLIC TerminalObservation",f"TerminalObservation {'dq' if wide else 'dd'} {len(registers)+4} dup(0)",".code"]
    for variant in ["Literal","Corrected"]:
        start=variant+"Marker";end=start+"End";entry="Terminal"+variant
        lines += ["PUBLIC "+entry+", "+start+", "+end,entry+" PROC"]
        lines += ["    push "+reg for reg in saved]
        lines += ["    mov rax,rcx","    bt rdx,0"] if wide else [f"    mov eax,[esp+{4*len(saved)+4}]",f"    bt DWORD PTR [esp+{4*len(saved)+8}],0"]
        lines += [f"    mov {reg},{value:016X}h" if wide else f"    mov {reg},0{value:08X}h" for reg,value in constants.items()]
        # MOV setup/capture preserves the selected carry and every status flag.
        lines += [f"    mov [TerminalObservation+{len(registers)*unit}],{sp}","    "+pushf,f"    {popf} [TerminalObservation+{(len(registers)+1)*unit}]"]
        if variant=="Literal":lines += [start+" LABEL BYTE",f"    mov DWORD PTR [{start}],0"]
        else:lines += ["    SMC_DOHALT "+start]
        lines += [end+" LABEL BYTE"]
        lines += [f"    mov [TerminalObservation+{index*unit}],{reg}" for index,reg in enumerate(registers)]
        lines += ["    "+pushf,f"    {popf} [TerminalObservation+{(len(registers)+2)*unit}]"]
        lines += [f"    lea {acc},{end}" if wide else f"    mov {acc},OFFSET {end}",f"    mov [TerminalObservation+{(len(registers)+3)*unit}],{acc}"]
        lines += ["    pop "+reg for reg in reversed(saved)]+["    ret",entry+" ENDP"]
    lines += ["END"]
    (folder/"terminal.asm").write_text("\n".join(lines)+"\n",encoding="utf-8")
    header=[f"using Word=std::uint{unit*8}_t;",f"constexpr unsigned RegisterCount={len(registers)};",
      "extern \"C\" { void TerminalLiteral(Word,unsigned); void TerminalCorrected(Word,unsigned);",
      "extern unsigned char LiteralMarker[], LiteralMarkerEnd[], CorrectedMarker[], CorrectedMarkerEnd[];",
      "extern Word TerminalObservation[]; }", "const Word ExpectedRegisters[]={0,0,"+
      ",".join(hex(value)+( "ULL" if wide else "U") for value in constants.values())+"};"]
    (folder/"terminal.hpp").write_text("\n".join(header)+"\n",encoding="utf-8")
    return registers
