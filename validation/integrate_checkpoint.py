"""Promote a reviewed immutable checkpoint with before-images and conflict protection."""
import hashlib,json,shutil,sys,tarfile
from datetime import datetime,timezone
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget();sys.stdout.reconfigure(encoding="utf-8")
def digest(path):
 h=hashlib.sha256()
 with path.open("rb") as stream:
  for part in iter(lambda:stream.read(1<<20),b""):h.update(part)
 return h.hexdigest()
plan=json.loads((ROOT/"validation/.build/checkpoint-integration-plan.json").read_text(encoding="utf-8"))
assert not plan["conflicts"],"Resolve local edits before promotion"
remote=Path(plan["remote"]);manifest=json.loads((remote.parent/"manifest.json").read_text(encoding="utf-8"))
assert manifest["commit"]==plan["commit"]
assert json.loads((remote.parent/"PULL_VERIFIED.json").read_text())["passed"] is True
report=json.loads((remote/"validation/remote-evidence/lean.json").read_text(encoding="utf-8"))
assert report["passed"] is True and report["toolchain"]=="leanprover/lean4:v4.35.0-rc3"
assert report["commit"]=="470d5ce1400764999581fd26d5d72b00d990b0f4"
assert digest(remote/"validation/remote-evidence/lean.json")==manifest["checkpoint"]["audit"]["report_sha256"]
for name,expected in report["sources"].items():assert digest(remote/name)==expected,name
for record in report["declarations"]:assert set(record["axioms"])<={"propext","Classical.choice","Quot.sound"}
current={p.relative_to(remote).as_posix() for p in (remote/"lean").glob("*.lean")}
current|={p.relative_to(remote).as_posix() for p in (remote/"lean/SmcTuring").rglob("*.lean")}
assert current=={n for n in report["sources"] if n.endswith(".lean")}
changes=[r for r in plan["changes"] if not r["path"].endswith(".log") or r["path"].startswith("validation/ci/reference/")]
for item in changes:
 name=item["path"];path=ROOT/name
 assert not Path(name).is_absolute() and ".." not in Path(name).parts
 assert name.startswith(("lean/","smcTuring/","output/pdf/","validation/",".github/workflows/")) or name in ["CHECKPOINT.md","REMOTE_STATUS.json","README.md"]
 assert not name.startswith(("validation/remote/","validation/remote-evidence/","validation/remote-agent/"))
 assert ".git" not in Path(name).parts and ".lake" not in Path(name).parts
 assert (digest(path) if path.is_file() else None)==item["local"],"Local changed during review: "+name
 assert digest(remote/name)==item["remote"],"Immutable checkpoint altered: "+name
 if item.get("merged_path"):
  staged=Path(item["merged_path"]).resolve();assert staged.is_relative_to((ROOT/"validation/.build/integration-staged").resolve())
  assert digest(staged)==item["expected"],"Staged merge changed: "+name
stamp=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
backup=ROOT/"validation/remote/157.181.172.78/20261006/integrations"/(stamp+"-"+plan["commit"][:12]);backup.mkdir(parents=True,exist_ok=False)
for item in changes:
 name=item["path"];target=ROOT/name
 if target.is_file():
  before=backup/"before"/name;before.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(target,before)
 target.parent.mkdir(parents=True,exist_ok=True)
 temp=target.with_name(target.name+".checkpoint-tmp");shutil.copyfile(Path(item["merged_path"]) if item.get("merged_path") else remote/name,temp)
 assert digest(temp)==item.get("expected",item["remote"]);temp.replace(target)
 assert digest(target)==item.get("expected",item["remote"])
# Bind integrated source closure to the Linux report, while leaving Linux evidence separate.
for name,expected in report["sources"].items():
 if name.startswith("lean/"):assert digest(ROOT/name)==expected,"Integrated proof differs: "+name
record={"commit":plan["commit"],"integrated_at":datetime.now(timezone.utc).isoformat(),"snapshot":str(remote),"backup":str(backup),"changes":changes,
 "remote_audit":{"passed":True,"modules":len(report["modules"]),"declarations":len(report["declarations"]),"report_sha256":digest(remote/"validation/remote-evidence/lean.json")},
 "base_commit":plan.get("base_commit"),"preserved_local":plan.get("local_only",[]),"local_validation":{"state":"pending"},"preserved":["AGENTS.md","local resource/toolchain and collector settings","Windows evidence reports and compiled artifacts","original C++/ASM sources"]}
(backup/"integration.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
(ROOT/"validation/remote/157.181.172.78/20261006/latest-integration.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print("Integrated "+str(len(changes))+" source/document/status files from "+plan["commit"]+"; before-images at "+str(backup))
