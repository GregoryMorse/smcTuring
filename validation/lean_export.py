"""Direct pinned Lean command with complete import artifacts and resource flags."""
import json
from pathlib import Path
from module_artifacts import ArtifactResolver,TOOLCHAIN
from memory_budget import require_budget,ROOT
_RESOLVER=ArtifactResolver()
_CACHE={}
def lean_command(project: Path,binary: Path,arguments: list[str]) -> list[str]:
 require_budget()
 project=project.resolve()
 supplied=binary if binary.name.lower()=='lean.exe' else binary/'lean.exe'
 assert supplied.resolve()==(TOOLCHAIN/'bin/lean.exe').resolve(),'Exporter toolchain differs'
 files=[arg for arg in arguments if arg.endswith('.lean')]
 assert len(files)==1,'Exactly one Lean source is required'
 source=(project/files[0]).resolve()
 relative=source.relative_to(project)
 assert source.is_file() and source.parent==project,'Unexpected exporter source'
 name='.'.join(relative.with_suffix('').parts)
 if name not in _CACHE:
  maps,levels=_RESOLVER.select(name)
  setup=ROOT/'validation/.build/export-setups'/(name+'.json')
  setup.parent.mkdir(parents=True,exist_ok=True)
  setup.write_text(json.dumps(dict(name=name,package='smcTuring',isModule=True,
   options={'autoImplicit':False},importArts=maps,dynlibs=[],plugins=[]),sort_keys=True),encoding='utf-8')
  _CACHE[name]=setup
 return [str(supplied),'-M768','-j1','--setup',str(_CACHE[name])]+arguments
