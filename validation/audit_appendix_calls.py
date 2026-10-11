"""Check the literal appendix CALL syntax under MASM NEAR-label typing.

This is finite assembler evidence; it does not execute the appendix or prove
hardware instruction semantics or a general assembler theorem.
"""
from datetime import date
import hashlib
import json
from pathlib import Path
import shutil
from audit_encoding import coff
from run_defaddr import vc_environment, run

ROOT = Path(__file__).resolve().parents[1]
PAPER_SHA256 = "adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    folder = ROOT / "validation/.build/appendix-calls"
    folder.mkdir(parents=True, exist_ok=True)
    environment = vc_environment("x86")
    assembler = shutil.which("ml.exe", path=environment["PATH"])
    assert assembler, "Missing x86 MASM"
    command = [assembler, "/nologo", "/c", "/safeseh", "/Fo"+str(folder/"calls.obj"),
               "/Fl"+str(folder/"calls.lst"), str(ROOT/"validation/appendix_calls.asm")]
    output = run(command, folder, environment)
    (folder/"build.log").write_text(output, encoding="utf-8")
    code, symbols, relocations = coff(folder/"calls.obj", "x86")
    cases = []
    for stem in ["AppendixBracket", "AppendixDirect", "AppendixIndirect"]:
        begin, end = symbols[stem], symbols[stem+"End"]
        packet = code[begin:end]
        local = {position-begin: kind for position, kind in relocations.items()
                 if begin <= position < end}
        if stem != "AppendixIndirect":
            assert packet == bytes.fromhex("e800000000") and not local
            form, offset = "callRelative", 1
        else:
            assert packet == bytes.fromhex("ff1505000000") and local == {2: 6}
            form, offset = "callIndirect", 2
        cases.append({"symbol": stem, "bytes": packet.hex(), "length": len(packet),
                      "form": form, "payload_offset": offset, "payload_width": 4,
                      "relocations": local})
    source_names = ["validation/audit_appendix_calls.py", "validation/appendix_calls.asm",
                    "validation/audit_encoding.py", "validation/run_defaddr.py",
                    "validation/.cache/morse-2018.pdf"]
    sources = {name: digest(ROOT/name) for name in source_names}
    assert sources["validation/.cache/morse-2018.pdf"] == PAPER_SHA256
    report = {"as_of": date.today().isoformat(), "passed": True,
              "architecture": "x86", "published_listing": 10,
              "scope": "MASM syntax and NEAR-code-label typing; no execution or general assembler proof",
              "assembler": assembler, "command": command, "sources": sources,
              "artifacts": {str((folder/name).relative_to(ROOT)): digest(folder/name)
                            for name in ["calls.obj", "calls.lst"]}, "cases": cases}
    (ROOT/"validation/appendix-calls.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print("Appendix CALL: PASS literal bracketed NEAR label = E8 rel32 (5 bytes, field +1); "
          "explicit DWORD PTR = FF /2 (6 bytes, field +2)")


if __name__ == "__main__":
    main()
