"""Place the unchanged pure Listing 10 blocks in all 24 region orders.

Host initialization/observation remains outside the pure block intervals.
Each core retains prefix, CALL and fall continuation contiguously. Inputs,
DEFSTACK and taken continuation may precede or follow that core.
"""
from itertools import permutations
from pathlib import Path
import json
import re
from generate_branch import generate as generate_reference

ROOT = Path(__file__).resolve().parents[1]
ORDERS = list(permutations(["stack", "core", "taken", "data"]))


def renamed(value, original, replacement):
    if isinstance(value, str):
        return value.replace(original, replacement)
    if isinstance(value, list):
        return [renamed(item, original, replacement) for item in value]
    if isinstance(value, dict):
        return {key:renamed(item, original, replacement) for key,item in value.items()}
    return value


def generate(folder: Path):
    reference = folder / "reference"
    originals = generate_reference(reference)
    asm = (reference / "branch.asm").read_text(encoding="utf-8").splitlines()
    header = (reference / "branch.hpp").read_text(encoding="utf-8")
    declarations, raw_entries = header.split("static const Fixture fixtures[] = {", 1)
    entries = raw_entries.split("};",1)[0].strip().rstrip(",").splitlines()
    entries = [line.rstrip(",") for line in entries]
    assert len(originals)==len(entries)==12 and len(ORDERS)==24
    lines = [".686", ".model flat, C", "option casemap:none", ".data"]
    fixtures, cpp_declarations, cpp_entries, procedures = [], [], [], []
    for geometry,order in enumerate(ORDERS):
        for original,entry in zip(originals,entries):
            old = original["name"]
            stem = "BranchG"+str(geometry).zfill(2)+"_"+old.removeprefix("Branch")
            labels = original["labels"]
            proc = old+" PROC uses ebx esi edi seed:DWORD, initialCarry:DWORD"
            first = asm.index(proc)
            stack = asm.index(labels["Stack"]+"::",first)
            start = asm.index(labels["Start"]+"::",stack)
            taken = asm.index(labels["Taken"]+"::",start)
            capture = asm.index(labels["Capture"]+"::",taken)
            endproc = asm.index(old+" ENDP",capture)
            data = asm.index(labels["X"]+":",endproc)
            end = asm.index(labels["ImageEnd"]+":",data)
            assert stack==first+1 and start>stack+2
            chunks = {
              "stack":asm[stack:stack+2],
              "core":asm[start:taken],
              "taken":asm[taken:capture],
              "data":[line.replace(labels["X"]+":",labels["X"]+"::").replace(labels["Y"]+":",labels["Y"]+"::") for line in asm[data:end]]+[old+"DataEnd::"]}
            # Keep the original initializer as host setup and emit the actual
            # inactive DEFSTACK owner separately at its chosen coordinate.
            host = [asm[first-1],proc,asm[stack+1]]+asm[stack+2:start]+["    jmp "+labels["Start"]]
            body = host+[line for role in order for line in chunks[role]]+asm[capture:endproc+1]+[labels["ImageEnd"]+":"]
            procedures.extend(line.replace(old,stem) for line in body)
            observation = labels["Observation"].replace(old,stem)
            lines += ["PUBLIC "+observation,observation+" DWORD 12 DUP(0)"]
            for line in declarations.splitlines():
                if re.search(r"\b"+re.escape(old)+r"(?:Observation|X|Y|Mask|Delta|Call|Stack|Start|Fall|Taken|ImageEnd)?(?:\(|\[|;)",line):
                    cpp_declarations.append(line.replace(old,stem))
            cpp_entries.append(entry.replace(old,stem))
            fixture = renamed(original,old,stem)
            fixture["geometry_order"] = list(order)
            fixture["geometry_index"] = geometry
            fixtures.append(fixture)
    lines += [".code"]+procedures+["END"]
    folder.mkdir(parents=True,exist_ok=True)
    (folder/"branch.asm").write_text("\n".join(lines)+"\n",encoding="utf-8")
    (folder/"branch.hpp").write_text("\n".join(cpp_declarations)+"\nstatic const Fixture fixtures[] = {\n"+",\n".join(cpp_entries)+"\n};\n",encoding="utf-8")
    (folder/"manifest.json").write_text(json.dumps(fixtures,indent=2)+"\n",encoding="utf-8")
    native=(ROOT/"validation/branch_native.cpp").read_text(encoding="utf-8")
    native=native.replace('int main() {', 'int main(int argc, char** argv) {')
    native=native.replace('        unsigned total=0;', '        const unsigned selected = argc==2 ? static_cast<unsigned>(std::stoul(argv[1])) : 24u;\n        require(selected < 24u || argc==1, \"Invalid geometry\");\n        unsigned total=0, fixtureIndex=0;')
    native=native.replace('        for (const auto& f : fixtures) {', '        for (const auto& f : fixtures) {\n            const unsigned geometry = fixtureIndex++/12u;\n            if (selected < 24u && selected != geometry) continue;')
    native=native.replace('require(total == 74400, "Unexpected total");',
      'require(total == (selected < 24u ? 74400u : 6200u*(sizeof(fixtures)/sizeof(fixtures[0]))), "Unexpected total");')
    native=native.replace('(12 relations, GPR/ESP/CF/word/code frames)',
      '(24 region orders, 12 relation modes, GPR/ESP/CF/word/code frames)')
    (folder/"harness.cpp").write_text(native,encoding="utf-8")
    return fixtures


if __name__=="__main__":
    generate(ROOT/"validation/.build/branch_geometries")
