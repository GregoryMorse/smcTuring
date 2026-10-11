"""Execute and bind the exact 19/21-byte cursor trace to local Lean evidence."""
from datetime import date
import json,os,shutil,subprocess
from pathlib import Path
from audit_encoding import coff
from bounded_build import CHAIN,COMMIT,digest
from lean_export import lean_command
from generate_cursor import generate,ROOT
from memory_budget import require_budget
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def execute_arch(arch):
 folder=ROOT/'validation/.build/cursor'/arch;generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env['PATH']);assert value,name;return value
 asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/I'+str(ROOT/'smcTuring'),
  '/Fo'+str(folder/'cursor.obj'),'/Fl'+str(folder/'cursor.lst')]
 asm+=['/DX64'] if arch=='x64' else ['/safeseh']
 asm+=[str(folder/'cursor.asm')]
 commands=[asm,[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/I'+str(folder),
  '/c',str(ROOT/'validation/cursor_native.cpp'),'/Fo'+str(folder/'harness.obj')],
  [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'cursor.exe'),
   str(folder/'cursor.obj'),str(folder/'harness.obj')]]
 (folder/'build.log').write_text(''.join(run(command,folder,env) for command in commands),encoding='utf-8')
 output=run([str(folder/'cursor.exe')],folder,env);assert 'PASS 204800 cases' in output,output
 (folder/'run.log').write_text(output,encoding='utf-8');print(output.strip(),flush=True)
 project=ROOT/'lean';binary=project/'.elan/toolchains'/CHAIN.replace('/','--').replace(':','---')/'bin/lean.exe'
 assert (project/'lean-toolchain').read_text(encoding='utf-8').strip()==CHAIN
 export_env=dict(env);export_env['SMCTURING_CURSOR_SITES']=str(folder/'cursor-packets.json')
 export_env['SMCTURING_CURSOR_ARCH']=arch
 command=lean_command(project,binary,['--run','ExportCursor.lean'])
 exported=subprocess.run(command,cwd=project,env=export_env,capture_output=True,text=True,
  encoding='utf-8',errors='replace',timeout=120)
 assert exported.returncode==0,exported.stdout+exported.stderr
 reference=json.loads(exported.stdout);actual=json.loads((folder/'cursor-packets.json').read_text(encoding='utf-8'))
 for key in ['pc','cursor','head','endpoint','initial','owners','live']:
  assert actual[key]==reference[key],(arch,key,actual[key],reference[key])
 span=19 if arch=='x86' else 21
 assert len(reference['checks'])==8 and all(reference['checks'])
 assert len(actual['live'])==40 and len(actual['initial'])==span
 assert all(len(row['bytes'])==span for row in actual['live'])
 code,symbols,relocations=coff(folder/'cursor.obj',arch);section,targets=relocation_targets(folder/'cursor.obj',arch)
 start=symbols['CursorMarker'];base=actual['pc']-start
 assert symbols['CursorMarkerEnd']==start+span
 assert reference['middle']==base+symbols['CursorXor']
 assert actual['cursor']==base+symbols['CursorPointer'] and actual['head']==base+symbols['CursorTape']
 assert symbols['CursorPointer']-symbols['CursorOwner']==(1 if arch=='x86' else 2)
 assert symbols['CursorTapeEnd']==symbols['CursorTape']+10
 firstSize=6 if arch=='x86' else 7;relOffset=2 if arch=='x86' else 3
 locations=[start+relOffset,start+firstSize+7+relOffset,symbols['CursorTape']+2]
 destinations=[actual['cursor'],actual['cursor'],actual['head']+6]
 sections=[(start,actual['initial']),(symbols['CursorOwner'],actual['owners'][0]),
  (symbols['CursorTape'],actual['owners'][1])]
 for position,packet in sections:
  expected=bytearray(packet);local={}
  for location,destination,kind in zip(locations,destinations,reference['relocations']):
   if position<=location<position+len(packet):
    target=targets[location];assert target['kind']==kind and target['section']==section
    offset=location-position
    expected[offset:offset+4]=((destination-base-target['value'])%(1<<32)).to_bytes(4,'little')
    local[offset]=kind
  assert {offset-position:kind for offset,kind in relocations.items() if position<=offset<position+len(packet)}==local
  assert bytes(expected)==code[position:position+len(packet)],(arch,position,expected.hex(),code[position:position+len(packet)].hex())
 above_dword=all(actual[key]>=(1<<32) for key in ['pc','cursor','head'])
 assert arch!='x64' or above_dword
 (folder/'lean-packets.json').write_text(json.dumps(reference,indent=2)+'\n',encoding='utf-8')
 (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'cursor.obj')],folder,env),encoding='utf-8')
 files=['cursor.asm','cursor.hpp','cursor.obj','cursor.lst','harness.obj','cursor.exe','build.log','run.log',
  'cursor-packets.json','lean-packets.json','native.disasm.txt']
 return dict(architecture=arch,passed=True,executions=204800,full_ax_words=16,symbols=40,
  code_images=41,owner_packets=2,compared_bytes=41*span+sum(map(len,actual['owners'])),
  instruction_bytes=span,relocations=3,static_checks=8,x64_addresses_above_4GiB=above_dword,
  full_ax_cursor_gpr_stack_defined_flags_endpoint_tape_code_frame_unmodified_reuse=True,
  commands=commands,export_command=command,
  artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),'/'):digest(folder/name) for name in files})

def main():
 require_budget()
 proof_path=ROOT/'validation/cursor_lean.json'
 proof=json.loads(proof_path.read_text(encoding='utf-8'))
 assert proof['passed'] and proof['toolchain']==CHAIN and proof['commit']==COMMIT
 for name,expected in proof['sources'].items():assert digest(ROOT/name)==expected,'Stale local Lean source: '+name
 names={entry['name'] for entry in proof['declarations']}
 required=['SmcTuring.Appendix.CursorLayout.checks_valid','SmcTuring.Appendix.CursorImage.correct',
  'SmcTuring.Appendix.CursorImage.pure','SmcTuring.Appendix.CursorImage.trace','SmcTuring.Appendix.CursorEffects.finish_effect']
 assert set(required)<=names
 runs=[execute_arch(arch) for arch in ['x86','x64']]
 sources=['validation/generate_cursor.py','validation/run_cursor.py','validation/cursor_native.cpp',
  'validation/generate_dword_owner.py','validation/generate_terminal.py','validation/run_terminal.py',
  'validation/run_defaddr.py','validation/audit_encoding.py','validation/bounded_build.py',
  'validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',
  'smcTuring/pure_smc.inc','smcTuring/dword_owner_smc.inc','lean/ExportCursor.lean']
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,
  complete_loaded_and_object_packets_checked=True,toolchain=CHAIN,commit=COMMIT,
  local_lean_audit_sha256=digest(proof_path),proofs=required,runs=runs,
  scope='Exact XCHG/full-width cursor, XOR DWORD [AX+6], XCHG trace. One finite original image, full AX/cursor restoration, current tape conditional symbol, SP/CF/PC and three owned writes are locally proved. Defined native flags/GPRs, complete packets/COFF targets and unchanged-image repeat invocation are independently tested. AF is undefined after XOR and excluded. Preceding actual XOR/AND operand patches, the whole Listing 8 body and whole-library fresh provenance remain separate.',
  sources={name:digest(ROOT/name) for name in sources})
 (ROOT/'validation/cursor.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print('Cursor native/model binding: PASS both modes, 204800 cases each, 41 images/two owners/three relocations/eight proved checks.',flush=True)
if __name__=='__main__':main()
