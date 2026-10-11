"""Resolve a regenerated PDF conflict only when local correction text is unchanged."""
import json
import unicodedata
from pathlib import Path
import fitz
from memory_budget import ROOT, require_budget

require_budget()
path = ROOT / "validation/.build/checkpoint-integration-plan.json"
plan = json.loads(path.read_text(encoding="utf-8"))
assert len(plan["conflicts"]) == 1
item = plan["conflicts"][0]
assert item["path"] == "output/pdf/morse-2018-errata.pdf"
def content(pdf_path):
    with fitz.open(pdf_path) as pdf:
        assert len(pdf) == 2
        text = unicodedata.normalize("NFKC", " ".join(page.get_text() for page in pdf))
        text = "".join(c for c in text if not 0xFE00 <= ord(c) <= 0xFE0F)
        # The local TeX renderer extracts the printed underscore as a space.
        return " ".join(text.split()).replace("MIN INT", "MIN_INT")
local = content(ROOT / item["path"])
base = content(Path(plan["base_snapshot"]) / item["path"])
assert local == base, "The local PDF has substantive edits; merge those before promoting"
remote = content(Path(plan["remote"]) / item["path"])
assert "M20." in remote and "DATAOFFS" in remote
item["strategy"] = "replace_superseded_pdf_preserve_before"
plan["changes"].append(item)
plan["conflicts"] = []
plan["pdf_rebuild_required"] = True
plan["pdf_conflict_resolution"] = "Local correction text equals the prior checkpoint after known PDF glyph/variation-selector extraction normalization; replacement includes M20 and the original local PDF is preserved as a before-image"
path.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
print("Resolved regenerated PDF conflict: old local correction text unchanged; preserve before-image and promote M20.")
