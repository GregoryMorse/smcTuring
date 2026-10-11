"""Run the main axiom audit with complete rc3 import artifacts and bounded Lean."""
import json,subprocess,sys
from pathlib import Path
from module_artifacts import ArtifactResolver,PROJECT,TOOLCHAIN
from memory_budget import require_budget,ROOT
require_budget()
sys.stdout.reconfigure(encoding='utf-8')
resolver=ArtifactResolver();maps,levels=resolver.select('Audit')
setup=ROOT/'validation/.build/main-audit-setup.json'
setup.write_text(json.dumps(dict(name='Audit',package='smcTuring',isModule=True,
 options={'autoImplicit':False},importArts=maps,dynlibs=[],plugins=[]),sort_keys=True),encoding='utf-8')
result=subprocess.run([str(TOOLCHAIN/'bin/lean.exe'),'-M768','-j1','Audit.lean','--setup',str(setup)],
 cwd=PROJECT,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=600)
print(result.stdout+result.stderr,end='',flush=True)
raise SystemExit(result.returncode)
