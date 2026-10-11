"""Extract the complete selected instruction entries from pinned primary PDFs."""
from pathlib import Path
import re
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
cache = ROOT / "validation/.cache/intel-093"
selections = {"vol2a": ["ADD", "AND", "CALL"], "vol2b": ["MOV", "SUB", "SBB"],
              "vol2d": ["XCHG", "XOR"]}
for name, instructions in selections.items():
    pattern = re.compile(r"(?m)^(?:" + "|".join(instructions) + r")\u2014[^\n]*Vol\.\s*2[A-D]\s+\d+-\d+")
    ordinary_mov = re.compile(r"(?m)^MOV\u2014Move\s+Vol\.")
    texts = []
    for index, page in enumerate(PdfReader(cache / (name+".pdf")).pages):
        text = page.extract_text()
        found = pattern.search(text)
        if found and (not found.group().startswith("MOV") or ordinary_mov.search(text)):
            texts.append(f"PDF page {index+1}\n{text}")
    assert texts, name
    (cache/(name+"-selected.txt")).write_text("\n\n".join(texts),encoding="utf-8")
    print(name, len(texts), "selected instruction pages",flush=True)
terms = ["Self-Modifying Code", "SELF-MODIFYING CODE", "MODIFYING CODE", "11.1.3"]
texts = []
for index, page in enumerate(PdfReader(cache / "vol3a.pdf").pages):
    text = page.extract_text()
    if any(term in text for term in terms):
        texts.append(f"PDF page {index+1}\n{text}")
(cache/"vol3a-selected.txt").write_text("\n\n".join(texts),encoding="utf-8")
print("vol3a",len(texts),"matched pages",flush=True)
