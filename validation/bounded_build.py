"""Compile project modules serially, binding cache entries to checked artifacts."""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
from memory_budget import require_budget,ROOT
from lean_build import lake_command
from module_artifacts import ArtifactResolver
sys.stdout.reconfigure(encoding='utf-8')
PROJECT=ROOT/'lean'
CACHE=PROJECT/'.lake/proof-build'
STATE=ROOT/'validation/.build/bounded-build.json'
CHAIN='leanprover/lean4:v4.35.0-rc3'
COMMIT='470d5ce1400764999581fd26d5d72b00d990b0f4'

def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for chunk in iter(lambda:stream.read(1<<20),b''):h.update(chunk)
 return h.hexdigest()

def imports_of(text):
 imports=[]
 for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)',text,re.M):
  for name in line.split('--',1)[0].split():
   if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',name):raise ValueError('Unsupported import: '+name)
   imports.append(name)
 return imports

def main():
 require_budget()
 parser=argparse.ArgumentParser();parser.add_argument('--force',action='store_true')
 parser.add_argument('--report');parser.add_argument('targets',nargs='+');args=parser.parse_args()
 chain=(PROJECT/'lean-toolchain').read_text().strip();assert chain==CHAIN
 binary=PROJECT/'.elan/toolchains'/chain.replace('/','--').replace(':','---')/'bin/lean.exe'
 lake_command(PROJECT,binary.parent) # Validate proof/editor configuration equivalence.
 version=subprocess.run([str(binary),'-M768','-j1','--version'],check=True,capture_output=True,text=True).stdout.strip()
 assert 'version 4.35.0-rc3,' in version and COMMIT in version,version
 state=json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {}
 context={str(p.relative_to(ROOT)):digest(p) for p in [
  binary,PROJECT/'lean-toolchain',PROJECT/'lakefile.toml',PROJECT/'lakefile.proof.toml',
  PROJECT/'lake-manifest.json',ROOT/'validation/bounded_build.py',ROOT/'validation/lean_build.py',ROOT/'validation/module_artifacts.py']}
 paths=[Path(p) for p in os.environ['LEAN_PATH'].split(os.pathsep)]
 paths.append(binary.parent.parent/'lib/lean')
 external={};resolver=ArtifactResolver();file_hashes={};header_hashes={}
 def cached_digest(path):
  key=str(path.relative_to(ROOT))
  if key not in file_hashes:file_hashes[key]=digest(path)
  return file_hashes[key]
 def external_artifact(name):
  if name in external:return external[name]
  stem=Path(*name.split('.'))
  match=next((base/stem for base in paths if (base/stem).with_suffix('.olean').is_file()),None)
  if match is None:raise FileNotFoundError('Missing imported artifact: '+name)
  files=[Path(str(match)+suffix) for suffix in ['.olean','.olean.server','.olean.private','.ir','.ir.sig']]
  external[name]={str(p.relative_to(ROOT)):cached_digest(p) for p in files if p.exists()}
  return external[name]
 done={};compiled=[]
 def visit(name):
  if name in done:return done[name]['fingerprint']
  relative=name.replace('.','/')
  source=PROJECT/(relative+'.lean');text=source.read_text(encoding='utf-8')
  imports=imports_of(text)
  dep_hashes={dep:visit(dep) for dep in imports if dep=='SmcTuring' or dep.startswith('SmcTuring.')}
  direct_external={dep:external_artifact(dep) for dep in imports if dep not in dep_hashes}
  setup=CACHE/'ir'/(relative+'.setup.json')
  maps,levels=resolver.select(name)
  setup_data=dict(plugins=[],package='smcTuring',options={'autoImplicit':False},
    name=name,isModule=True,importArts=maps,dynlibs=[])
  setup.parent.mkdir(parents=True,exist_ok=True)
  encoded_setup=json.dumps(setup_data,sort_keys=True)
  if not setup.exists() or setup.read_text(encoding='utf-8')!=encoded_setup:
   setup.write_text(encoded_setup,encoding='utf-8')
  selected={}
  for module,groups in maps.items():
   hashes={str(Path(path).relative_to(ROOT)):cached_digest(Path(path)) for group in groups for path in group}
   selected[module]=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest()
   imported_source,_=resolver.locate(module)
   key=str(imported_source.relative_to(ROOT))
   if key not in header_hashes:header_hashes[key]=digest(imported_source)
   if not module.startswith('SmcTuring'):external[module]=hashes
  fingerprint=hashlib.sha256(json.dumps([digest(source),dep_hashes,direct_external,selected,context,digest(setup)],sort_keys=True).encode()).hexdigest()
  object_file=CACHE/'lib/lean'/(relative+'.olean')
  files=[Path(str(object_file.with_suffix(''))+s) for s in ['.olean','.olean.server','.olean.private','.ir','.ir.sig','.ilean']]
  artifacts={str(p.relative_to(ROOT)):digest(p) for p in files if p.exists()}
  previous=state.get(name)
  fresh=not args.force and isinstance(previous,dict) and previous.get('input')==fingerprint and previous.get('artifacts')==artifacts and object_file.exists()
  if not fresh:
   object_file.parent.mkdir(parents=True,exist_ok=True)
   c_file=CACHE/'ir'/(relative+'.c');c_file.parent.mkdir(parents=True,exist_ok=True)
   assert source==PROJECT/(relative+'.lean'),'Unexpected compilation source'
   command=[str(binary),'-M768','-j1',str(source),'-o',str(object_file),'-i',
    str(object_file.with_suffix('.ilean')),'-c',str(c_file),'--setup',str(setup)]
   result=subprocess.run(command,cwd=PROJECT,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=600)
   log=ROOT/'validation/.build/bounded-modules'/(relative+'.log')
   log.parent.mkdir(parents=True,exist_ok=True);log.write_text(result.stdout+result.stderr,encoding='utf-8')
   print(name+' exit '+str(result.returncode),flush=True)
   if result.returncode:
    print(result.stdout+result.stderr,flush=True);raise SystemExit(result.returncode)
   compiled.append(name)
   artifacts={str(p.relative_to(ROOT)):digest(p) for p in files if p.exists()}
   assert object_file.exists() and artifacts,name
  record=dict(input=fingerprint,artifacts=artifacts,source=digest(source),setup_sha256=digest(setup),
   import_levels={mod:list(level) for mod,level in levels.items() if mod!=name})
  record['fingerprint']=hashlib.sha256(json.dumps(record,sort_keys=True).encode()).hexdigest()
  state[name]=record;STATE.parent.mkdir(parents=True,exist_ok=True)
  STATE.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
  done[name]=record;return record['fingerprint']
 for target in args.targets:visit(target)
 if args.report:
  report=dict(passed=True,version=version,toolchain=CHAIN,context=context,modules=done,
   external_artifacts=external,import_header_sources=header_hashes,compiled=compiled,targets=args.targets)
  path=Path(args.report);path.parent.mkdir(parents=True,exist_ok=True)
  path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print('Serial bounded build passed: '+str(len(done))+' modules inspected; '+str(len(compiled))+' compiled.',flush=True)
if __name__=='__main__':main()
