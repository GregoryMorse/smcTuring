"""Reproduce the local cursor build and 63-declaration kernel audit."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
from bounded_build import COMMIT,CHAIN,imports_of,digest
from memory_budget import ROOT,require_budget
from lean_export import lean_command
require_budget()
sys.stdout.reconfigure(encoding='utf-8')
project=ROOT/'lean'
binary=project/'.elan/toolchains'/CHAIN.replace('/','--').replace(':','---')/'bin/lean.exe'
build_report=ROOT/'validation/.build/cursor-build-cachecheck.json'
result=subprocess.run([sys.executable,str(ROOT/'validation/bounded_build.py'),'--report',
 str(build_report),'SmcTuring.Appendix.CursorImage'],capture_output=True,text=True,
 encoding='utf-8',errors='replace',timeout=1200)
print(result.stdout+result.stderr,end='',flush=True)
assert result.returncode==0,'Bounded build failed'
command=lean_command(project,binary,['AuditCursor.lean'])
result=subprocess.run(command,cwd=project,capture_output=True,text=True,
 encoding='utf-8',errors='replace',timeout=120)
log=ROOT/'validation/.build/cursor-audit-current.log'
output=result.stdout+result.stderr
log.write_text(output,encoding='utf-8')
assert result.returncode==0,output
expected=re.findall(r'^#print axioms (\S+)',(project/'AuditCursor.lean').read_text(encoding='utf-8'),re.M)
pattern=r"^'([^'\r\n]+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(?:does not depend on any axioms))"
declarations=[]
for match in re.finditer(pattern,output,re.M):
 name,axioms=match.groups()
 found=re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',axioms or '')
 assert set(found)<={'propext','Classical.choice','Quot.sound'},(name,found)
 declarations.append(dict(name=name,axioms=found))
assert len(expected)==63 and len(set(expected))==63
assert [entry['name'] for entry in declarations]==expected,output
build=json.loads(build_report.read_text(encoding='utf-8'))
assert build['passed'] and COMMIT in build['version']
paths={project/(module.replace('.','/')+'.lean') for module in build['modules']}
for path in paths:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',path.read_text(encoding='utf-8')),path
paths.update(ROOT/name for name in [
 'AGENTS.md','lean/AuditCursor.lean','lean/lean-toolchain','lean/lakefile.toml',
 'lean/lakefile.proof.toml','lean/lake-manifest.json','validation/bounded_build.py',
 'validation/lean_build.py','validation/limited_run.py','validation/memory_budget.py',
 'validation/check_memory_budget.py','validation/lean_export.py','validation/module_artifacts.py','validation/run_cursor_lean.py'])
report=dict(passed=True,
 scope=f"63 local mixed DWORD/full-width cursor declarations and their checked {len(build['modules'])}-module dependency closure; whole-library audit remains pending; native cursor evidence is recorded separately",
 toolchain=CHAIN,commit=COMMIT,version=build['version'],
 declarations=declarations,sources={str(p.relative_to(ROOT)):digest(p) for p in sorted(paths)},
 build=build,audit=dict(command=command,exit=result.returncode,log=str(log.relative_to(ROOT)),
 sha256=digest(log)),memory_policy=dict(aggregate_allocation_limit_bytes=1500000000,
 resident_stop_threshold_bytes=1500000000,resident_sample_interval_ms=25,
 lean_memory_mb=768,lean_threads=1,serial=True))
(ROOT/'validation/cursor_lean.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Cursor build and local kernel audit passed: 63 declarations, standard axioms only.')
