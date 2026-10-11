"""Bind the printed five-instruction update to current Lean/kernel evidence."""
from datetime import date
import json,os,shutil,subprocess
from pathlib import Path
from audit_encoding import coff
from bounded_build import CHAIN,COMMIT,digest
from lean_export import lean_command
from generate_input_update import generate,ROOT
from memory_budget import require_budget
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def execute_arch(arch):
 folder=ROOT/'validation/.build/input_update'/arch;generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env['PATH']);assert value,name;return value
 asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/I'+str(ROOT/'smcTuring'),
  '/Fo'+str(folder/'update.obj'),'/Fl'+str(folder/'update.lst')]
 asm+=['/DX64'] if arch=='x64' else ['/safeseh']
 asm+=[str(folder/'update.asm')]
 commands=[asm,[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/I'+str(folder),
  '/c',str(ROOT/'validation/input_update_native.cpp'),'/Fo'+str(folder/'harness.obj')],
  [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/MANIFEST:EMBED',
   "/MANIFESTUAC:level='asInvoker' uiAccess='false'",'/OUT:'+str(folder/'update.exe'),
   str(folder/'update.obj'),str(folder/'harness.obj')]]
 (folder/'build.log').write_text(''.join(run(command,folder,env) for command in commands),encoding='utf-8')
 output=run([str(folder/'update.exe')],folder,env);assert 'PASS 204800 cases' in output,output
 (folder/'run.log').write_text(output,encoding='utf-8');print(output.strip(),flush=True)
 project=ROOT/'lean';binary=project/'.elan/toolchains'/CHAIN.replace('/','--').replace(':','---')/'bin/lean.exe'
 assert (project/'lean-toolchain').read_text(encoding='utf-8').strip()==CHAIN
 export_env=dict(env);export_env['SMCTURING_UPDATE_SITES']=str(folder/'input-update-packets.json')
 export_env['SMCTURING_UPDATE_ARCH']=arch
 export_command=lean_command(project,binary,['--run','ExportInputUpdate.lean'])
 exported=subprocess.run(export_command,cwd=project,env=export_env,capture_output=True,text=True,
  encoding='utf-8',errors='replace',timeout=120)
 assert exported.returncode==0,exported.stdout+exported.stderr
 reference=json.loads(exported.stdout);actual=json.loads((folder/'input-update-packets.json').read_text(encoding='utf-8'))
 for key in ['pc','cursor','head','endpoint','initial','object','owners','live']:
  assert actual[key]==reference[key],(arch,key,actual[key],reference[key])
 span=39 if arch=='x86' else 41
 assert len(reference['checks'])==10 and all(reference['checks'])
 assert len(actual['live'])==40 and len(actual['initial'])==len(actual['object'])==span
 assert all(len(row['bytes'])==span for row in actual['live'])
 code,symbols,relocations=coff(folder/'update.obj',arch);section,targets=relocation_targets(folder/'update.obj',arch)
 start=symbols['UpdateMarker'];base=actual['pc']-start
 assert symbols['UpdateMarkerEnd']==start+span and symbols['UpdateBody']==start+20
 assert symbols['UpdateNew']==start and symbols['UpdateMask']==start+10
 assert reference['field']==base+symbols['UpdateXor']+3
 assert actual['cursor']==base+symbols['UpdatePointer'] and actual['head']==base+symbols['UpdateTape']
 assert symbols['UpdatePointer']-symbols['UpdateOwner']==(1 if arch=='x86' else 2)
 assert symbols['UpdateTapeEnd']==symbols['UpdateTape']+10
 firstSize=6 if arch=='x86' else 7;relOffset=2 if arch=='x86' else 3
 locations=[start+2,start+12,start+20+relOffset,start+20+firstSize+7+relOffset,symbols['UpdateTape']+2]
 destinations=[reference['field'],reference['field'],actual['cursor'],actual['cursor'],actual['head']+6]
 sections=[(start,actual['object']),(symbols['UpdateOwner'],actual['owners'][0]),
  (symbols['UpdateTape'],actual['owners'][1])]
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
 above_dword=all(actual[key]>=(1<<32) for key in ['pc','cursor','head']) and reference['field']>=(1<<32)
 assert arch!='x64' or above_dword
 (folder/'lean-packets.json').write_text(json.dumps(reference,indent=2)+'\n',encoding='utf-8')
 (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'update.obj')],folder,env),encoding='utf-8')
 files=['update.asm','update.hpp','update.obj','update.lst','harness.obj','update.exe','build.log','run.log',
  'input-update-packets.json','lean-packets.json','native.disasm.txt']
 return dict(architecture=arch,passed=True,executions=204800,full_ax_words=16,symbols=40,
  prepared_code_images=41,force_wide_object_image=1,owner_packets=2,
  compared_bytes=42*span+sum(map(len,actual['owners'])),
  instruction_bytes=span,relocations=5,static_checks=10,x64_addresses_above_4GiB=above_dword,
  full_ax_cursor_gpr_stack_defined_flags_endpoint_tape_operand_code_frame_caller_reinitialized_reuse=True,
  commands=commands,export_command=export_command,
  artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),'/'):digest(folder/name) for name in files})

def main():
 require_budget()
 proof_path=ROOT/'validation/input_update_lean.json'
 proof=json.loads(proof_path.read_text(encoding='utf-8'))
 assert proof['passed'] and proof['toolchain']==CHAIN and proof['commit']==COMMIT
 for name,expected in proof['sources'].items():assert digest(ROOT/name)==expected,'Stale local Lean source: '+name
 names={entry['name'] for entry in proof['declarations']}
 required=['SmcTuring.Appendix.InputUpdate.checks_valid','SmcTuring.Appendix.InputUpdateTrace.original_correct',
  'SmcTuring.Appendix.InputUpdateTrace.pure','SmcTuring.Appendix.InputUpdateTrace.trace',
  'SmcTuring.Appendix.InputUpdateTrace.effect','SmcTuring.Appendix.InputUpdateTrace.retained_image']
 assert set(required)<=names
 runs=[execute_arch(arch) for arch in ['x86','x64']]
 sources=['validation/generate_input_update.py','validation/run_input_update.py','validation/input_update_native.cpp',
  'validation/generate_cursor.py','validation/generate_dword_owner.py','validation/generate_terminal.py','validation/run_terminal.py',
  'validation/run_defaddr.py','validation/audit_encoding.py','validation/bounded_build.py',
  'validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',
  'smcTuring/pure_smc.inc','smcTuring/dword_owner_smc.inc','lean/ExportInputUpdate.lean']
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,
  complete_loaded_and_object_packets_checked=True,toolchain=CHAIN,commit=COMMIT,
  local_lean_audit_sha256=digest(proof_path),proofs=required,runs=runs,
  scope='Printed XOR/AND/XCHG/XOR/XCHG update: 39/41 bytes, current operand decoded after actual earlier writes, selected tape value, full AX/cursor restoration, exact two-field memory result, retained complete image and five owned writes. Native defined flags/GPRs, full prepared and force-wide original object packets, COFF targets, and caller current-symbol reinitialized repeat invocation are independently tested. Placeholder CNSTFRC32 forces immediate width; execution uses the proved match mask. AF after XOR is undefined and excluded. Whole Listing 8 setup/comparison/node/loop/finalization and whole-library freshness remain separate.',
  sources={name:digest(ROOT/name) for name in sources})
 (ROOT/'validation/input_update.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print('Input update native/model binding: PASS both modes, 204800 cases each, 41 prepared images/original object/two owners/five relocations/ten proved checks.',flush=True)
if __name__=='__main__':main()
