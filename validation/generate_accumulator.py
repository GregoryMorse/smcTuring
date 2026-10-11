"""Literal Listing 9 order, a pure output-producing body and corrected DOHALT."""
from itertools import permutations
from pathlib import Path
from generate_terminal import generate as terminal_generate
ROOT=Path(__file__).resolve().parents[1]
ORDERS=list(permutations(["Save","Pointer","Body"]))

def generate(folder,arch):
    folder.mkdir(parents=True,exist_ok=True)
    bootstrap=folder/"bootstrap";registers=terminal_generate(bootstrap,arch)
    text=(bootstrap/"terminal.asm").read_text(encoding="utf-8")
    header=text.split("PUBLIC TerminalLiteral",1)[0].replace("TerminalObservation","AccumulatorObservation")
    header=header.replace("include terminal_smc.inc","include pure_smc.inc\ninclude terminal_smc.inc")
    leading=text.split("TerminalLiteral PROC\n",1)[1].split("LiteralMarker LABEL BYTE",1)[0].replace("TerminalObservation","AccumulatorObservation")
    trailing=text.split("LiteralMarkerEnd LABEL BYTE\n",1)[1].split("TerminalLiteral ENDP",1)[0].replace("TerminalObservation","AccumulatorObservation")
    acc=registers[0];wide=arch=="x64";offset=2 if wide else 1
    unit=8 if wide else 4
    constants=[0,0]+[0x12340000+i*0x01010101+(0x7654321000000000 if wide else 0) for i in range(2,len(registers))]
    lines=[header];fixtures=[];cpp=[f"static_assert(sizeof(Word)=={unit}, \"word size\");",f"constexpr unsigned RegisterCount={len(registers)};",
      "extern \"C\" { extern Word AccumulatorObservation[];"]
    for index,order in enumerate(ORDERS):
        prefix="A"+str(index)
        names={name:prefix+name for name in ["Entry","Prologue","BodyFirst","BodySecond","BodyStore","Epilogue","Second","Third","Marker","MarkerEnd","OwnersEnd"]}
        names.update({name+suffix:prefix+name+suffix for name in ["Save","Pointer","Body","Output"] for suffix in ["Owner","Field"]})
        cpp+=["void "+names["Entry"]+"(Word,unsigned);","extern unsigned char "+",".join(names[name]+"[]" for name in names if name!="Entry")+";"]
        lines += ["PUBLIC "+", ".join(names.values()),names["Entry"]+" PROC",leading]
        lines += [names["Prologue"]+"::",f"    mov [{names['SaveField']}],{acc}",names["BodyFirst"]+"::",f"    xchg {acc},[{names['BodyField']}]",
          names["BodySecond"]+"::",f"    mov [{names['BodyField']}],{acc}",names["BodyStore"]+"::",f"    mov [{names['OutputField']}],{acc}",names["Epilogue"]+"::",
          f"    xchg {acc},[{names['PointerField']}]",names["Second"]+"::",f"    mov [{names['PointerField']}],{acc}",names["Third"]+"::",f"    xchg {acc},[{names['SaveField']}]",
          "    SMC_DOHALT "+names["Marker"],names["MarkerEnd"]+"::",trailing.replace("LiteralMarkerEnd",names["MarkerEnd"]),names["Entry"]+" ENDP"]
        for name in list(order)+["Output"]:
            lines += [names[name+"Owner"]+" LABEL BYTE","    MOFFSMOV "+names[name+"Field"]+", "+( "OFFSET "+names["SaveField"] if name=="Pointer" else "0")]
        lines += [names["OwnersEnd"]+" LABEL BYTE"]
        fixtures.append(dict(index=index,order=list(order),names=names,owner_offset=offset))
    lines += ["END"];(folder/"accumulator.asm").write_text("\n".join(lines)+"\n",encoding="utf-8")
    cpp += ["}","const Word ExpectedRegisters[]={"+",".join(hex(v)+("ULL" if wide else "U") for v in constants)+"};","const Fixture Fixtures[]={"]
    for fixture in fixtures:
        names=fixture["names"]
        cpp += ['{'+str(fixture['index'])+','+names['Entry']+','+','.join(names[name] for name in ["Prologue","BodyFirst","BodySecond","BodyStore","Epilogue","Second","Third","Marker","MarkerEnd","SaveOwner","PointerOwner","BodyOwner","OutputOwner","SaveField","PointerField","BodyField","OutputField","OwnersEnd"])+"},"]
    cpp += ["};"]
    (folder/"accumulator.hpp").write_text("\n".join(cpp)+"\n",encoding="utf-8")
    (folder/"manifest.json").write_text(__import__('json').dumps(fixtures,indent=2)+"\n",encoding="utf-8")
    return fixtures
