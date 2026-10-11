"""Plan an incremental checkpoint promotion, preserving local notes and artifacts."""
import hashlib,json,subprocess,sys
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget();sys.stdout.reconfigure(encoding="utf-8")
def digest(p):
 if not p.is_file():return None
 h=hashlib.sha256()
 with p.open("rb") as f:
  for b in iter(lambda:f.read(1<<20),b""):h.update(b)
 return h.hexdigest()
previous=json.loads((ROOT/"validation/remote/157.181.172.78/20261006/latest-integration.json").read_text(encoding="utf-8"))
latest=json.loads((ROOT/"validation/remote/157.181.172.78/20261006/codex-checkpoints/latest-local.json").read_text(encoding="utf-8"))
remote=Path(latest["project"]);base=Path(previous["snapshot"])
manifest=json.loads((remote.parent/"manifest.json").read_text(encoding="utf-8"));old=json.loads((base.parent/"manifest.json").read_text(encoding="utf-8"))
assert manifest["commit"]==latest["commit"] and old["commit"]==previous["commit"]
assert json.loads((remote.parent/"PULL_VERIFIED.json").read_text())["passed"] is True
stage=ROOT/"validation/.build/integration-staged"/latest["commit"];stage.mkdir(parents=True,exist_ok=True)
changes=[];conflicts=[];preserved=[];unchanged=0
sources=manifest["checkpoint"]["sources"];old_sources=old["checkpoint"]["sources"]
supplement=remote.parent/"SUPPLEMENT_VERIFIED.json"
if supplement.exists():
 receipt=json.loads(supplement.read_text(encoding="utf-8"))
 assert receipt["passed"] and receipt["commit"]==latest["commit"]
 package_path="validation/ci-results/portable-source-package.json"
 assert digest(remote/package_path)==receipt["package_sha256"]==sources[package_path]
 package=json.loads((remote/package_path).read_text(encoding="utf-8"))
 for n,rh in receipt["supplementary_hashes"].items():
  assert n in {".github/workflows/proof-native.yml",".github/workflows/palomar-full.yml"} and rh==package["sources"][n] and digest(remote/n)==rh
  sources[n]=rh
def allowed(n):
 if n in {"AGENTS.md","TURN_CHECKPOINT.json"} or (n.endswith(".log") and not n.startswith("validation/ci/reference/")):return False
 if n.startswith(("validation/remote/","validation/remote-evidence/","validation/remote-agent/")):return False
 if n.startswith("validation/") and n.endswith(".json") and not n.startswith("validation/ci/"):return False
 return n.startswith(("lean/","smcTuring/","output/pdf/","validation/",".github/workflows/")) or n in {"CHECKPOINT.md","REMOTE_STATUS.json","README.md"}
for n,rh in sources.items():
 if not allowed(n):continue
 path=ROOT/n;bp=base/n;rp=remote/n;bh=old_sources.get(n);lh=digest(path)
 assert digest(rp)==rh,"Altered immutable checkpoint: "+n
 if rh==bh:
  if lh!=bh:preserved.append(n)
  else:unchanged+=1
  continue
 if lh==rh:unchanged+=1;continue
 item={"path":n,"base":bh,"local":lh,"remote":rh,"strategy":"direct","expected":rh}
 if lh==bh or lh is None:
  changes.append(item);continue
 output=stage/n;output.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith(".md") and bp.is_file():
  b=bp.read_text(encoding="utf-8");l=path.read_text(encoding="utf-8");r=rp.read_text(encoding="utf-8")
  if l.startswith(b):
   output.write_text(r+l[len(b):],encoding="utf-8");item["strategy"]="preserve_local_append"
  else:
   result=subprocess.run(["git","merge-file","-p",str(path),str(bp),str(rp)],capture_output=True)
   if result.returncode:conflicts.append(item);continue
   output.write_bytes(result.stdout);item["strategy"]="three_way_text"
 elif n=="REMOTE_STATUS.json":
  b=json.loads(bp.read_text(encoding="utf-8"));l=json.loads(path.read_text(encoding="utf-8"));r=json.loads(rp.read_text(encoding="utf-8"))
  if {k:v for k,v in l.items() if k!="coordinator_integration"}!=b:conflicts.append(item);continue
  if "coordinator_integration" in l:r["coordinator_integration"]=l["coordinator_integration"]
  output.write_text(json.dumps(r,indent=2)+"\n",encoding="utf-8");item["strategy"]="preserve_coordinator_metadata"
 else:conflicts.append(item);continue
 item["merged_path"]=str(output);item["expected"]=digest(output);changes.append(item)
deleted=[n for n in old_sources if allowed(n) and n not in sources]
assert not deleted,"Review remote deletions before integrating: "+repr(deleted)
plan={"commit":latest["commit"],"base_commit":previous["commit"],"remote":str(remote),"base_snapshot":str(base),"changes":changes,"conflicts":conflicts,"local_only":preserved,"unchanged":unchanged,"previous_integration":previous}
(ROOT/"validation/.build/checkpoint-integration-plan.json").write_text(json.dumps(plan,indent=2)+"\n",encoding="utf-8")
print("Plan: "+str(len(changes))+" promotions; "+str(len(conflicts))+" conflicts; preserved local-only "+repr(preserved))
for r in changes:
 if r["strategy"]!="direct":print("Merge: "+r["path"]+" ("+r["strategy"]+")")
assert not conflicts,"Resolve genuine local conflicts before applying the plan"
