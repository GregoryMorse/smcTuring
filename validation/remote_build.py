"""Pinned Linux verification in an enforced remote cgroup; no native-test claims."""
import argparse,hashlib,json,os,re,subprocess,sys,threading,time,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
TASK=ROOT.parent
CHAIN="leanprover/lean4:v4.35.0-rc3"
COMMIT="470d5ce1400764999581fd26d5d72b00d990b0f4"
LIMIT=7_500_000_000
EVIDENCE=ROOT/"validation/remote-evidence"
EVIDENCE.mkdir(parents=True,exist_ok=True)
def digest(path):
 h=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1<<20),b""):h.update(block)
 return h.hexdigest()
def checkpoint(name,data):
 path=EVIDENCE/(name+".json")
 temp=path.with_suffix(".tmp")
 temp.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
 temp.replace(path)
def run(command,cwd=None,env=None):
 print("RUN "+repr(command),flush=True)
 subprocess.run(command,cwd=cwd or ROOT/"lean",env=env,check=True)
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--force',action='store_true',help='Cold project replay; ignore verified module reuse')
 parser.add_argument('--refresh-dependencies',action='store_true',help='Explicitly refresh the pinned Mathlib cache')
 args=parser.parse_args()
 group=next(line.split("::",1)[1] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
 cgroup=Path("/sys/fs/cgroup")/group.lstrip("/")
 cap=int((cgroup/"memory.max").read_text().strip())
 assert 0<cap<=LIMIT,(group,cap)
 assert (cgroup/"memory.swap.max").read_text().strip()=="0"
 stop=threading.Event();peak=[0]
 def sample():
  while not stop.wait(.1):
   try:peak[0]=max(peak[0],int((cgroup/"memory.current").read_text()))
   except OSError:return
 monitor=threading.Thread(target=sample,daemon=True);monitor.start()
 status=1
 try:
  assert (ROOT/"lean/lean-toolchain").read_text().strip()==CHAIN
  release=json.loads((TASK/"lean-release.json").read_text())
  asset=next(item for item in release["assets"] if item["name"]=="lean-4.35.0-rc3-linux.tar.zst")
  expected=asset["digest"].removeprefix("sha256:")
  archive=TASK/asset["name"];partial=archive.with_suffix(archive.suffix+".partial")
  toolroot=TASK/"toolchain";toolroot.mkdir(exist_ok=True)
  compiler=toolroot/"lean-4.35.0-rc3-linux"
  if not (compiler/"bin/lean").is_file():
   if not archive.is_file() or digest(archive)!=expected:
    request=urllib.request.Request(asset["browser_download_url"],headers={"User-Agent":"smcTuring-proof"})
    with urllib.request.urlopen(request,timeout=60) as source,partial.open("wb") as output:
     while True:
      block=source.read(1<<20)
      if not block:break
      output.write(block)
    assert digest(partial)==expected,"Release archive hash differs"
    partial.replace(archive)
   listing=subprocess.run(["tar","--zstd","-tf",str(archive)],capture_output=True,text=True,check=True).stdout
   for entry in listing.splitlines():
    parts=Path(entry).parts
    assert parts and parts[0]==compiler.name and ".." not in parts,entry
   run(["tar","--zstd","-xf",str(archive),"-C",str(toolroot)],cwd=TASK)
  env=dict(os.environ)
  env["PATH"]=str(compiler/"bin")+os.pathsep+env["PATH"]
  env["LEAN_NUM_THREADS"]="8"
  env["RAYON_NUM_THREADS"]="1"
  env["MATHLIB_CACHE_DIR"]=str(TASK/"cache/mathlib")
  version=subprocess.run([str(compiler/"bin/lean"),"--version"],capture_output=True,text=True,check=True).stdout.strip()
  assert "version 4.35.0-rc3," in version and COMMIT in version,version
  binary_sha256=digest(compiler/"bin/lean")
  toolchain_record=dict(toolchain=CHAIN,version=version,archive_sha256=expected,
   binary_sha256=binary_sha256,remote_memory_limit_bytes=cap,threads=8)
  cache_env=dict(env)
  # The bundled curl needs its built-in provider configuration on RHEL.
  # Retain certificate verification using the host's installed CA trust store.
  if Path('/etc/pki/tls/certs/ca-bundle.crt').is_file():
   cache_env['OPENSSL_CONF']='/dev/null'
   cache_env['CURL_CA_BUNDLE']='/etc/pki/tls/certs/ca-bundle.crt'
  manifest=json.loads((ROOT/"lean/lake-manifest.json").read_text())
  pins=json.loads((ROOT/"validation/ci/pins.json").read_text(encoding="utf-8"))
  assert next(p["rev"] for p in manifest["packages"] if p["name"]=="mathlib")==pins["mathlib_revision"]
  os.environ["SMCTURING_LEAN_ROOT"]=str(compiler)
  from remote_artifacts import ArtifactResolver
  from remote_reuse import read_previous,reusable,input_fingerprint
  resolver=ArtifactResolver();project=ROOT/"lean";cache=project/".lake/proof-build"
  env["LEAN_PATH"]=os.pathsep.join([str(project/".lake/packages"/p["name"]/".lake/build/lib/lean") for p in reversed(manifest["packages"])]+[str(cache/"lib/lean")])
  source_paths=list(project.glob("*.lean"))+list((project/"SmcTuring").rglob("*.lean"))
  sources={str(path.relative_to(ROOT)):digest(path) for path in source_paths}
  for name in ["lean/lean-toolchain","lean/lakefile.proof.toml","lean/lake-manifest.json","validation/remote_build.py","validation/remote_artifacts.py","validation/remote_reuse.py"]:
   sources[name]=digest(ROOT/name)
  # Bind the runnable final validation package without treating Python/JSON/PDF
  # inputs as Lean modules or changing the complete-map compilation path.
  ci_paths=list((ROOT/"validation/ci").glob("*.py"))+list((ROOT/"validation/ci").glob("*.json"))
  ci_paths+=list((ROOT/".github/workflows").glob("*.yml"))
  ci_paths+=[p for p in (ROOT/"validation/ci/reference").rglob("*") if p.is_file()]
  for path in ci_paths:sources[path.relative_to(ROOT).as_posix()]=digest(path)
  context=dict(toolchain=CHAIN,commit=COMMIT,version=version,compiler_sha256=binary_sha256,
   options={"autoImplicit":False},heap_mb=6000,threads=8)
  # Read old compiler/audit provenance BEFORE replacing either record.
  previous=read_previous(EVIDENCE,context,sources)
  checkpoint("toolchain",toolchain_record)
  dependencies_refreshed=[False]
  def refresh_dependencies():
   run([str(compiler/"bin/lake"),"-f","lakefile.proof.toml","exe","cache","get"],env=cache_env)
   dependencies_refreshed[0]=True
  if args.refresh_dependencies or not previous:refresh_dependencies()
  def select(name):
   try:return resolver.select(name)
   except FileNotFoundError:
    if dependencies_refreshed[0]:raise
    refresh_dependencies();return resolver.select(name)
  done={};artifacts={};hashes={};compiled=[0];reused=[0]
  def cached_digest(path):
   key=str(path.relative_to(TASK))
   if key not in hashes:hashes[key]=digest(path)
   return hashes[key]
  def compile_module(name):
   if name in done:return
   relative=name.replace(".","/");source=project/(relative+".lean")
   imports=[]
   for line in re.findall(r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)",source.read_text(encoding="utf-8"),re.M):
    imports+=line.split("--",1)[0].split()
   for child in imports:
    if child=="SmcTuring" or child.startswith("SmcTuring."):compile_module(child)
   maps,levels=select(name)
   setup=cache/"ir"/(relative+".setup.json");setup.parent.mkdir(parents=True,exist_ok=True)
   setup.write_text(json.dumps(dict(name=name,package="smcTuring",isModule=True,
    options={"autoImplicit":False},importArts=maps,dynlibs=[],plugins=[]),sort_keys=True),encoding="utf-8")
   obj=cache/"lib/lean"/(relative+".olean");obj.parent.mkdir(parents=True,exist_ok=True)
   command=[str(compiler/"bin/lean"),"-M6000","-j8",str(source),"-o",str(obj),
    "-i",str(obj.with_suffix(".ilean")),"-c",str(cache/"ir"/(relative+".c")),"--setup",str(setup)]
   produced=[Path(str(obj.with_suffix(""))+suffix) for suffix in [".olean",".olean.server",".olean.private",".ir",".ir.sig",".ilean"]]
   inputs={str(path.relative_to(TASK)):cached_digest(path) for groups in maps.values() for group in groups for path in map(Path,group)}
   outputs={str(path.relative_to(ROOT)):digest(path) for path in produced if path.is_file()}
   source_hash=sources[str(source.relative_to(ROOT))];setup_hash=digest(setup)
   hit=reusable(previous,name,source_hash,command,setup_hash,inputs,outputs,force=args.force)
   if hit:reused[0]+=1
   else:
    result=subprocess.run(command,cwd=project,env=env,capture_output=True,text=True,encoding="utf-8")
    log=EVIDENCE/(relative.replace("/","-")+".log");log.write_text(result.stdout+result.stderr,encoding="utf-8")
    print(name+" exit "+str(result.returncode),flush=True)
    assert result.returncode==0,result.stdout+result.stderr
    outputs={str(path.relative_to(ROOT)):digest(path) for path in produced if path.is_file()}
    # Invalidate memoized hashes after replacing a child's artifacts.
    for path in produced:hashes.pop(str(path.relative_to(TASK)),None)
    compiled[0]+=1
   record=dict(source=source_hash,command=command,setup_sha256=setup_hash,
    artifacts=outputs,input_artifacts_sha256=input_fingerprint(inputs),cache_hit=hit)
   done[name]=record
   for module,groups in maps.items():
    for path in [Path(p) for group in groups for p in group]:artifacts[str(path.relative_to(TASK))]=cached_digest(path)
   if not hit or len(done)%64==0:
    checkpoint("build-progress",dict(modules=done,source_hashes=sources,compiled=len(done),
     kernel_compiled=compiled[0],verified_reused=reused[0],passed=False))
  compile_module("SmcTuring")
  if (project/"Solution.lean").is_file():compile_module("Solution")
  checkpoint("build-progress",dict(modules=done,source_hashes=sources,compiled=len(done),
   kernel_compiled=compiled[0],verified_reused=reused[0],passed=False))
  maps,levels=select("Audit")
  setup=EVIDENCE/"audit-setup.json"
  setup.write_text(json.dumps(dict(name="Audit",package="smcTuring",isModule=True,
   options={"autoImplicit":False},importArts=maps,dynlibs=[],plugins=[]),sort_keys=True),encoding="utf-8")
  command=[str(compiler/"bin/lean"),"-M6000","-j8","Audit.lean","--setup",str(setup)]
  result=subprocess.run(command,cwd=project,env=env,capture_output=True,text=True,encoding="utf-8")
  output=result.stdout+result.stderr
  (EVIDENCE/"axiom-audit.log").write_text(output,encoding="utf-8")
  assert result.returncode==0,output
  expected=re.findall(r"^#print axioms (\S+)",(project/"Audit.lean").read_text(),re.M)
  pattern=r"^'([^'\r\n]+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(?:does not depend on any axioms))"
  declarations=[]
  for match in re.finditer(pattern,output,re.M):
   name,axioms=match.groups();found=re.findall(r"[A-Za-z_][A-Za-z0-9_.]*",axioms or "")
   assert set(found)<={"propext","Classical.choice","Quot.sound"},(name,found)
   declarations.append(dict(name=name,axioms=found))
  assert [record["name"] for record in declarations]==expected and len(set(expected))==len(expected)
  for path in source_paths:
   # Palomar deliberately permits theorem holes in its independent Challenge.
   # Every production/Solution source remains subject to the strict token gate.
   if path==project/"Challenge.lean":continue
   assert not re.search(r"\b(sorry|admit|axiom|native_decide|Lean\.ofReduceBool)\b",path.read_text()),path
  for name,expected_hash in sources.items():assert digest(ROOT/name)==expected_hash,"Source changed during verification: "+name
  checkpoint("lean",dict(passed=True,scope="Complete uploaded SmcTuring library and requested axiom audit; native Windows tests remain separate",
   toolchain=CHAIN,commit=COMMIT,version=version,sources=sources,modules=done,
   imported_artifacts=artifacts,declarations=declarations,audit_command=command,
   audit_sha256=digest(EVIDENCE/"axiom-audit.log"),cache_context=context,
   kernel_compiled=compiled[0],verified_reused=reused[0],force_replay=args.force))
  status=0
  print("Remote kernel audit passed: "+str(len(declarations))+" declarations; "+str(compiled[0])+" compiled, "+str(reused[0])+" verified reused.",flush=True)
 finally:
  stop.set();monitor.join()
  checkpoint("resource",dict(exit=status,memory_limit_bytes=cap,
   sampled_peak_cgroup_memory_bytes=peak[0],cgroup=group,lean_threads=8,
   lean_memory_mb=6000,remote_only=True))
if __name__=="__main__":main()
