"""Final source/cache/protected-file integrity check for the integrated checkpoint."""
import hashlib,json,shutil,tarfile
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
def digest(path):
 h=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1<<20),b""):h.update(block)
 return h.hexdigest()
record=json.loads((ROOT/"validation/remote/157.181.172.78/20261006/latest-integration.json").read_text(encoding="utf-8"))
snapshot=Path(record["snapshot"]);remote=json.loads((snapshot/"validation/remote-evidence/lean.json").read_text(encoding="utf-8"))
for name,expected in remote["sources"].items():
 if name.startswith("lean/"):assert digest(ROOT/name)==expected,name
actual={p.relative_to(ROOT).as_posix() for p in (ROOT/"lean").glob("*.lean")}|{p.relative_to(ROOT).as_posix() for p in (ROOT/"lean/SmcTuring").rglob("*.lean")}
assert actual=={n for n in remote["sources"] if n.endswith(".lean")},"Proof source closure differs"
build_report=record["local_validation"].get("build_report")
build=None
if build_report:
 build=json.loads((ROOT/build_report).read_text(encoding="utf-8"));assert build["passed"]
 for name,expected in build["context"].items():assert digest(ROOT/name)==expected,name
 for name,module in build["modules"].items():
  assert digest(ROOT/"lean"/(name.replace(".","/")+".lean"))==module["source"],name
  assert digest(ROOT/"lean/.lake/proof-build/ir"/(name.replace(".","/")+".setup.json"))==module["setup_sha256"],name
  for artifact,expected in module["artifacts"].items():assert digest(ROOT/artifact)==expected,artifact
else:
 assert record["local_validation"]["state"]=="source_integrity_and_errata_passed_all_changed_windows_pending"
 assert not record["local_validation"]["targeted_axiom_audit_performed"]
protected=[]
with tarfile.open(ROOT/"validation/.build/remote-agent-sources.tar") as archive:
 for item in archive:
  if item.isfile() and (item.name.startswith("smcTuring/") or (item.name.startswith("validation/") and item.name.endswith(".json") and "/" not in item.name[len("validation/"):])):
   expected=hashlib.sha256(archive.extractfile(item).read()).hexdigest()
   assert digest(ROOT/item.name)==expected,"Protected baseline/native evidence changed: "+item.name
   protected.append(item.name)
assert not (ROOT/"lean/CheckpointDeltaAudit.lean").exists()
assert record["local_pdf_after_rebuild_sha256"]==digest(ROOT/"output/pdf/morse-2018-errata.pdf")
checked=len(build["targets"]) if build else 0
result={"passed":True,"checkpoint":record["commit"],"source_closure_matched":True,"delta_modules":checked,"dependency_closure":len(build["modules"]) if build else 0,"windows_proof_check_performed":build is not None,"protected_baseline_and_native_files":protected,"full_windows_build_passed":False,"scope":"Integrated source closure and preserved original/native evidence; "+("successful changed-module cache/artifact provenance checked; " if build else "no new Windows proof/cache check performed; ")+"full Windows/native verification remains pending"}
(ROOT/"validation/.build/checkpoint-final-integrity.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
shutil.copyfile(ROOT/"validation/.build/checkpoint-final-integrity.json",Path(record["local_evidence_archive"])/"checkpoint-final-integrity.json")
print("Final integrity passed: exact checkpoint proof sources; "+str(checked)+" checked changed modules; "+str(len(protected))+" protected source/evidence files unchanged.")
