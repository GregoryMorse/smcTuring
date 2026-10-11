"""Render the updated errata and the exact published pages needed for its new correction."""
import hashlib
import json
import subprocess
from memory_budget import ROOT, require_budget

require_budget()
plan = json.loads((ROOT/"validation/.build/checkpoint-integration-plan.json").read_text(encoding="utf-8"))
inventory = json.loads((ROOT/"lean/errata/edits.json").read_text(encoding="utf-8"))
directory = ROOT/"tmp/pdfs"/plan["commit"][:12]
directory.mkdir(parents=True, exist_ok=True)
pdf = ROOT/"output/pdf/morse-2018-errata.pdf"
subprocess.run(["pdftoppm", "-r", "130", "-png", str(pdf), str(directory/"errata")], check=True, timeout=90)
source = ROOT/inventory["source"]
for page, index in [(124, 2), (127, 5)]:
    subprocess.run(["pdftoppm", "-f", str(index), "-l", str(index), "-r", "130", "-png", str(source), str(directory/f"published-{page}")], check=True, timeout=90)
images = sorted(directory.glob("*.png"))
assert len(images) == 4
record = {"checkpoint": plan["commit"], "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
          "images": [str(p) for p in images], "visual_inspection_complete": False}
(ROOT/"validation/.build/checkpoint-errata-render.json").write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
print("Rendered two errata pages and published pp.124/127 at " + str(directory))
