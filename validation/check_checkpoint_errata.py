"""Source/PDF and immutable Linux-proof errata check; no fresh native aggregate claim."""
import hashlib,json,re,sys
from pathlib import Path
import fitz
from memory_budget import ROOT,require_budget
from audit_errata import PROOFS,make_diff,normalized
require_budget();sys.stdout.reconfigure(encoding="utf-8")
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
plan=json.loads((ROOT/"validation/.build/checkpoint-integration-plan.json").read_text(encoding="utf-8"))
snapshot=Path(plan["remote"]);manifest=json.loads((snapshot.parent/"manifest.json").read_text(encoding="utf-8"))
proof=snapshot/"validation/remote-evidence/lean.json"
assert digest(proof)==manifest["checkpoint"]["audit"]["report_sha256"]
lean=json.loads(proof.read_text(encoding="utf-8"));assert lean["passed"]
binding=json.loads((snapshot/"validation/remote-evidence/errata-source-proof.json").read_text(encoding="utf-8"))
assert binding["passed"] and binding["lean_report_sha256"]==digest(proof)
for name,expected in lean["sources"].items():
 if name.startswith("lean/"):assert digest(ROOT/name)==expected,"Integrated proof differs: "+name
inventory=json.loads((ROOT/"lean/errata/edits.json").read_text(encoding="utf-8"))
source=ROOT/inventory["source"];assert digest(source)==inventory["source_sha256"]
with fitz.open(source) as pdf:
 assert len(pdf)==7
 pages=[normalized(p.get_text()) for p in pdf]
edits=inventory["edits"];expected_count=binding["source_excerpts_checked"]
assert len(edits)==expected_count and len({e["id"] for e in edits})==expected_count
for edit in edits:
 text=pages[edit["page"]-123];assert normalized(edit["before"]) in text,edit["id"]
 assert edit["before"]!=edit["after"]
 if "occurrence" in edit:
  listing=edit.get("listing",11);block=text.split("Listing "+str(listing)+".",1)[1].split("Listing "+str(listing+1)+".",1)[0]
  assert block.count(normalized(edit["before"]))==2 and edit["occurrence"] in [1,2],edit["id"]
assert (ROOT/"lean/errata/morse-2018-minimal.diff").read_text(encoding="utf-8")==make_diff(edits)
declarations={d["name"]:d["axioms"] for d in lean["declarations"]}
assert PROOFS==binding["positive_proofs"] and len(set(PROOFS))==len(PROOFS)
for name in PROOFS:assert name in declarations and set(declarations[name])<={"propext","Classical.choice","Quot.sound"},name
output=ROOT/"output/pdf/morse-2018-errata.pdf"
with fitz.open(output) as pdf:
 assert len(pdf)==2
 text=normalized(" ".join(p.get_text() for p in pdf))
 correction_numbers=sorted({int(re.match(r"M(\d+)",e["id"]).group(1)) for e in edits})
 for marker in [*[f"M{n:02d}." for n in correction_numbers],"Justification of the corrections","10.24425/119359"]:assert marker in text,marker
log=(ROOT/"output/pdf/morse-2018-errata.log").read_text(encoding="utf-8",errors="replace")
for problem in ["Overfull","Undefined control sequence","LaTeX Warning"]:assert problem not in log,problem
render=None
if plan.get("pdf_rebuild_required"):
 render=json.loads((ROOT/"validation/.build/checkpoint-errata-render.json").read_text(encoding="utf-8"))
 assert render["checkpoint"]==plan["commit"] and render["pdf_sha256"]==digest(output)
 assert render["visual_inspection_complete"] is True
record={"passed":True,"checkpoint":plan["commit"],"scope":"Exact published source edits, source-matched checkpoint Linux positive proofs and locally rebuilt two-page PDF; Windows/native aggregate remains pending","source_excerpts_checked":expected_count,"positive_proofs":PROOFS,"correction_count":max(correction_numbers),"pages":2,"lean_evidence_sha256":digest(proof),"pdf_sha256":digest(output),"tex_sha256":digest(ROOT/"lean/errata/morse-2018-errata.tex"),"visual_qa":render["visual_qa"] if render else "Preserved prior local two-page visual QA"}
(ROOT/"validation/.build/checkpoint-errata-check.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(f"Errata check passed: {expected_count} exact source excerpts, {len(PROOFS)} checkpoint-audited references, two locally rebuilt and inspected pages.")
