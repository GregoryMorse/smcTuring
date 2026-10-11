"""Audit registered declarations of integrated changed modules under the local guard."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
from memory_budget import ROOT,require_budget
from module_artifacts import ArtifactResolver,TOOLCHAIN
require_budget();sys.stdout.reconfigure(encoding="utf-8")
plan=json.loads((ROOT/"validation/.build/checkpoint-integration-plan.json").read_text(encoding="utf-8"))
project=ROOT/"lean";build_path=ROOT/plan.get("validation_build_report","validation/.build/checkpoint-delta-build.json");build=json.loads(build_path.read_text(encoding="utf-8"))
assert build["passed"]
modules=[r["path"][5:-5].replace("/",".") for r in plan["changes"] if r["path"].startswith("lean/SmcTuring/") and r["path"].endswith(".lean")]
requested_modules=modules
modules=plan.get("validation_targets",modules)
assert set(modules)<=set(requested_modules)
assert build["targets"]==modules,"Changed-module build belongs to a different integration plan"
for name,record in build["modules"].items():
 assert hashlib.sha256((project/(name.replace(".","/")+".lean")).read_bytes()).hexdigest()==record["source"],"Stale changed-module source: "+name
namespaces=set(modules)
for mod in modules:
 source=(project/(mod.replace(".","/")+".lean")).read_text(encoding="utf-8")
 namespaces.update(re.findall(r"^namespace (SmcTuring[.][A-Za-z0-9_.]+)",source,re.M))
expected=[n for n in re.findall(r"^#print axioms (\S+)",(project/"Audit.lean").read_text(encoding="utf-8"),re.M) if any(n.startswith(ns+".") for ns in namespaces)]
assert expected and len(expected)==len(set(expected))
source=project/"CheckpointDeltaAudit.lean";assert not source.exists(),"Refusing to overwrite an existing source"
try:
 source.write_text("module\n"+"\n".join("public import "+m for m in modules)+"\npublic section\n"+"\n".join("#print axioms "+n for n in expected)+"\n",encoding="utf-8")
 maps,levels=ArtifactResolver().select("CheckpointDeltaAudit")
 setup=ROOT/"validation/.build/checkpoint-delta-audit-setup.json"
 setup.write_text(json.dumps(dict(name="CheckpointDeltaAudit",package="smcTuring",isModule=True,options={"autoImplicit":False},importArts=maps,dynlibs=[],plugins=[]),sort_keys=True),encoding="utf-8")
 command=[str(TOOLCHAIN/"bin/lean.exe"),"-M768","-j1",str(source),"--setup",str(setup)]
 result=subprocess.run(command,cwd=project,capture_output=True,text=True,encoding="utf-8",timeout=600)
 output=result.stdout+result.stderr
 log=ROOT/"validation/.build/checkpoint-delta-axiom-audit.log";log.write_text(output,encoding="utf-8")
 assert result.returncode==0,output[-3000:]
 pattern=r"^'([^'\r\n]+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(?:does not depend on any axioms))"
 declarations=[]
 for match in re.finditer(pattern,output,re.M):
  name,axioms=match.groups();found=re.findall(r"[A-Za-z_][A-Za-z0-9_.]*",axioms or "")
  assert set(found)<={"propext","Classical.choice","Quot.sound"},(name,found)
  declarations.append({"name":name,"axioms":found})
 assert [d["name"] for d in declarations]==expected
 record={"passed":True,"scope":f"Registered declarations in the {len(modules)} changed production modules; full Windows rebuild remains pending","checkpoint":plan["commit"],"requested_changed_modules":len(requested_modules),"partial_windows_scope":len(modules)<len(requested_modules),"build_report":str(build_path),"modules":modules,"declarations":declarations,"command":command,"build_report_sha256":hashlib.sha256(build_path.read_bytes()).hexdigest(),"axiom_log_sha256":hashlib.sha256(log.read_bytes()).hexdigest()}
 (ROOT/"validation/.build/checkpoint-delta-audit.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
 print("Changed-module axiom audit passed: "+str(len(declarations))+" declarations; standard axioms only.")
finally:
 if source.exists():
  preserved=ROOT/"validation/.build/CheckpointDeltaAudit.lean";preserved.write_bytes(source.read_bytes());source.unlink()
