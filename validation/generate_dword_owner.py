"""Generate the existing printed DEFDATA32 scalar owner in both modes."""
from pathlib import Path
from generate_terminal import generate as terminal_generate
ROOT=Path(__file__).resolve().parents[1]

def generate(folder,arch):
 folder.mkdir(parents=True,exist_ok=True);bootstrap=folder/'bootstrap';registers=terminal_generate(bootstrap,arch)
 text=(bootstrap/'terminal.asm').read_text(encoding='utf-8')
 header=text.split('PUBLIC TerminalLiteral',1)[0].replace('TerminalObservation','OwnerObservation').replace('include terminal_smc.inc','include dword_owner_smc.inc')
 section=text.split('TerminalCorrected PROC\n',1)[1]
 leading=section.split('    SMC_DOHALT CorrectedMarker\n',1)[0].replace('TerminalObservation','OwnerObservation')
 trailing=section.split('CorrectedMarkerEnd LABEL BYTE\n',1)[1].split('TerminalCorrected ENDP',1)[0].replace('TerminalObservation','OwnerObservation').replace('CorrectedMarkerEnd','OwnerMarkerEnd')
 lines=[header,'PUBLIC OwnerEntry, OwnerMarker, OwnerMarkerEnd','OwnerEntry PROC',leading,'    SMC_DEFDATA32 OwnerMarker,0','OwnerMarkerEnd LABEL BYTE',trailing,'OwnerEntry ENDP','END']
 (folder/'owner.asm').write_text('\n'.join(lines)+'\n',encoding='utf-8')
 baseline=(bootstrap/'terminal.hpp').read_text(encoding='utf-8')
 expected=baseline.split('const Word ExpectedRegisters[]=',1)[1]
 unit=8 if arch=='x64' else 4
 cpp=[f'using Word=std::uint{unit*8}_t;',f'constexpr unsigned RegisterCount={len(registers)};',
   'extern "C" { void OwnerEntry(Word,unsigned); extern unsigned char OwnerMarker[],OwnerMarkerEnd[]; extern Word OwnerObservation[]; }','const Word ExpectedRegisters[]='+expected]
 (folder/'owner.hpp').write_text('\n'.join(cpp)+'\n',encoding='utf-8')
 return registers
