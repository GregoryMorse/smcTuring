"""Typed published/corrected Listing 8 input-symbol helper fixtures."""
from pathlib import Path
from generate_terminal import generate as terminal_generate
ROOT=Path(__file__).resolve().parents[1]

def generate(folder,arch):
 folder.mkdir(parents=True,exist_ok=True);bootstrap=folder/"bootstrap";registers=terminal_generate(bootstrap,arch)
 text=(bootstrap/"terminal.asm").read_text(encoding="utf-8")
 header=text.split("PUBLIC TerminalLiteral",1)[0].replace("TerminalObservation","InputObservation").replace("include terminal_smc.inc","include pure_smc.inc")
 leading=text.split("TerminalLiteral PROC\n",1)[1].split("LiteralMarker LABEL BYTE",1)[0].replace("TerminalObservation","InputObservation")
 trailing=text.split("LiteralMarkerEnd LABEL BYTE\n",1)[1].split("TerminalLiteral ENDP",1)[0].replace("TerminalObservation","InputObservation")
 wide=arch=="x64";unit=8 if wide else 4;acc=registers[0]
 constants=[0,0]+[0x12340000+i*0x01010101+(0x7654321000000000 if wide else 0) for i in range(2,len(registers))]
 lines=[header];cpp=[f"static_assert(sizeof(Word)=={unit}, \"word size\");",f"constexpr unsigned RegisterCount={len(registers)};",
   "extern \"C\" { extern Word InputObservation[];"];fixtures=[]
 for index,variant in enumerate(["Literal","Corrected"]):
  names={name:variant+name for name in ["Entry","Start","Second","Third","Stop","Source","Target","Compare","End"]}
  cpp += ["void "+names["Entry"]+"(Word,unsigned);","extern unsigned char "+",".join(names[name]+"[]" for name in names if name!="Entry")+";"]
  source=names["Source"]+("+6" if variant=="Corrected" else "")
  lines += ["PUBLIC "+", ".join(names.values()),names["Entry"]+" PROC",leading,names["Start"]+"::",f"    xchg eax,DWORD PTR [{source}]",
    names["Second"]+"::",f"    mov DWORD PTR [{names['Target']}+3],eax",names["Third"]+"::",f"    xchg eax,DWORD PTR [{source}]",
    names["Stop"]+"::",trailing.replace("LiteralMarkerEnd",names["Stop"]),names["Entry"]+" ENDP",
    names["Source"]+" LABEL BYTE",f"    sub DWORD PTR [{names['Compare']}+6],80000000h",
    names["Target"]+" LABEL BYTE",f"    xor DWORD PTR [{acc}+6],80000000h",
    names["Compare"]+" LABEL BYTE",f"    mov DWORD PTR [{names['Compare']}+6],0",names["End"]+" LABEL BYTE"]
  fixtures.append(dict(index=index,corrected=variant=="Corrected",names=names))
 lines += ["END"];(folder/"input.asm").write_text("\n".join(lines)+"\n",encoding="utf-8")
 cpp += ["}","const Word ExpectedRegisters[]={"+",".join(hex(v)+("ULL" if wide else "U") for v in constants)+"};","const Fixture Fixtures[]={"]
 for f in fixtures:
  n=f['names'];cpp += ['{'+str(f['index'])+','+('true' if f['corrected'] else 'false')+','+n['Entry']+','+','.join(n[name] for name in ["Start","Second","Third","Stop","Source","Target","Compare","End"])+"},"]
 cpp += ["};"];(folder/"input.hpp").write_text("\n".join(cpp)+"\n",encoding="utf-8")
 (folder/"manifest.json").write_text(__import__('json').dumps(fixtures,indent=2)+"\n",encoding="utf-8")
 return fixtures
