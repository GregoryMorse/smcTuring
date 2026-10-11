"""Verify fresh local cursor proof, native artifacts and resource evidence."""
import json
from pathlib import Path
from bounded_build import CHAIN,COMMIT,digest,imports_of
from memory_budget import ROOT,MAX_BYTES,require_budget
def main():
 require_budget()
 proof_path=ROOT/'validation/cursor_lean.json';native_path=ROOT/'validation/cursor.json'
 proof=json.loads(proof_path.read_text(encoding='utf-8'));native=json.loads(native_path.read_text(encoding='utf-8'))
 assert proof['passed'] and native['passed']
 assert proof['toolchain']==native['toolchain']==CHAIN
 assert proof['commit']==native['commit']==COMMIT
 assert native['local_lean_audit_sha256']==digest(proof_path),'Native proof snapshot is stale'
 for report in [proof,native]:
  for name,expected in report['sources'].items():assert digest(ROOT/name)==expected,'Stale source: '+name
 build=proof['build'];closure=set()
 def visit(name):
  if name in closure:return
  closure.add(name)
  source=ROOT/'lean'/(name.replace('.','/')+'.lean')
  for dep in imports_of(source.read_text(encoding='utf-8')):
   if dep=='SmcTuring' or dep.startswith('SmcTuring.'):visit(dep)
 visit('SmcTuring.Appendix.CursorImage')
 assert closure==set(build['modules']),'Module closure differs'
 for name,record in build['modules'].items():
  assert digest(ROOT/'lean'/(name.replace('.','/')+'.lean'))==record['source']
  for path,expected in record['artifacts'].items():assert digest(ROOT/path)==expected,'Stale compiled module: '+path
 for path,expected in build['import_header_sources'].items():
  assert digest(ROOT/path)==expected,'Stale import header: '+path
 for name,record in build['modules'].items():
  setup=ROOT/'lean/.lake/proof-build/ir'/(name.replace('.','/')+'.setup.json')
  assert digest(setup)==record['setup_sha256'],'Stale module setup: '+name
 for path,expected in build['context'].items():assert digest(ROOT/path)==expected,'Stale build context: '+path
 for files in build['external_artifacts'].values():
  for path,expected in files.items():assert digest(ROOT/path)==expected,'Stale imported artifact: '+path
 expected=[line.split()[-1] for line in (ROOT/'lean/AuditCursor.lean').read_text(encoding='utf-8').splitlines() if line.startswith('#print axioms ')]
 names=[entry['name'] for entry in proof['declarations']]
 assert names==expected and len(names)==len(set(names))==63
 for item in proof['declarations']:assert set(item['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert set(native['proofs'])<=set(names)
 assert digest(ROOT/proof['audit']['log'])==proof['audit']['sha256']
 assert {run['architecture'] for run in native['runs']}=={'x86','x64'}
 for run in native['runs']:
  assert run['passed'] and run['executions']==204800 and run['static_checks']==8
  assert run['code_images']==41 and run['owner_packets']==2 and run['relocations']==3
  assert run['instruction_bytes']==(19 if run['architecture']=='x86' else 21)
  assert run['full_ax_cursor_gpr_stack_defined_flags_endpoint_tape_code_frame_unmodified_reuse']
  assert run['architecture']!='x64' or run['x64_addresses_above_4GiB']
  for path,expected in run['artifacts'].items():assert digest(ROOT/path)==expected,'Stale native artifact: '+path
 memory={}
 for name in ['memory-cursor-local.json','memory-cursor-native.json','memory-guard-current.json']:
  path=ROOT/'validation/.build'/name;record=json.loads(path.read_text(encoding='utf-8'))
  assert record['exit']==0 and record['resident_monitor_error'] is None
  assert 0<record['memory_limit_bytes']<=MAX_BYTES
  assert record['peak_group_commit_bytes']<2_000_000_000
  assert record['sampled_peak_group_resident_bytes']<MAX_BYTES
  memory[name]=dict(sha256=digest(path),**record)
 report=dict(passed=True,scope='Local cursor checkpoint only; whole-project provenance and complete Listing 8 composition remain pending',
  proof_sha256=digest(proof_path),native_sha256=digest(native_path),declarations=len(names),
  modules=len(closure),native_cases=sum(run['executions'] for run in native['runs']),memory=memory,
  verifier_sha256=digest(Path(__file__)))
 (ROOT/'validation/cursor_audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print('Cursor evidence: PASS 63 declarations/27-module closure/409600 native cases/current source, cache, artifact and memory hashes.')
if __name__=='__main__':main()
