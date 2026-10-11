"""Build, inspect and execute the normalized whole Listing 10 x86 fixture.

Finite native/assembler evidence is kept distinct from Lean byte refinement.
A crash, timeout or wrong result is a failed fixture, never an intended halt.
"""
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
from audit_encoding import coff
from generate_branch import generate
from lean_export import lean_command
from run_defaddr import vc_environment, run

ROOT = Path(__file__).resolve().parents[1]
PAPER_SHA256 = "adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def value_of(value, symbols):
    if isinstance(value, int):
        return value
    if "symbol" in value:
        return symbols[value["symbol"]]+value["add"]
    first, second = value["difference"]
    return symbols[first]-symbols[second]+value["add"]



def code_relocation_targets(path):
    # Resolve the referenced COFF symbol, not just the raw relocation addend.
    # IMAGE_REL_I386_DIR32 is 0x0006 in Microsoft's PE/COFF specification.
    data = path.read_bytes()
    machine,count,_,symbol_start,symbol_count,optional_size,_ = struct.unpack_from("<HHIIIHH",data)
    assert machine == 0x14c
    sections = [struct.unpack_from("<8sIIIIIIHHI",data,20+optional_size+40*i) for i in range(count)]
    chosen = [i for i,section in enumerate(sections) if section[0].rstrip(b"\0") == b".text$mn"]
    assert len(chosen) == 1
    section_number = chosen[0]+1
    section = sections[chosen[0]]
    targets = {}
    index = 0
    while index < symbol_count:
        _,value,number,_,_,auxiliary = struct.unpack_from("<8sIhHBB",data,symbol_start+index*18)
        targets[index] = (value,number)
        index += 1+auxiliary
    result = {}
    for i in range(section[7]):
        position,symbol,kind = struct.unpack_from("<IIH",data,section[5]+10*i)
        assert symbol in targets and position not in result
        value,number = targets[symbol]
        result[position] = {"value":value,"section":number,"kind":kind}
    return section_number,result


def encoded_address(value,position,targets,section):
    target = targets[position]
    assert target["kind"] == 6 and target["section"] == section, "Address outside fixture code section"
    return ((value-target["value"]) % (1 << 32)).to_bytes(4,"little")


def inspect(folder, fixtures, shapes, layouts, spaced):
    code, symbols, relocations = coff(folder/"branch.obj", "x86")
    section,targets = code_relocation_targets(folder/"branch.obj")
    canonical_shapes = {tuple(shape["bytes"]):shape for shape in shapes}
    assert len(canonical_shapes) == len(shapes) == 13
    reference_layouts = {(item["signed"],item["relation"]):item for item in layouts}
    assert len(reference_layouts) == len(layouts) == 12
    spaced_layouts = {(item["signed"],item["relation"]):item for item in spaced}
    assert len(spaced_layouts) == len(spaced) == 12
    observed_shapes = set()
    results = []
    for fixture in fixtures:
        labels = fixture["labels"]
        fields = {name: symbols[symbol]+offset for name,(symbol,offset) in fixture["fields"].items()}
        intervals = sorted((position,position+4,name) for name,position in fields.items())
        assert len(set(fields.values())) == 7
        assert all(left[1] <= right[0] for left,right in zip(intervals, intervals[1:])), "Overlapping fields"
        assert fields["pointer"]-4 == fields["address"]
        assert fields["pointer"] == symbols[labels["Stack"]]+6
        assert symbols[labels["Fall"]] == symbols[labels["Call"]]+5
        headers = []
        checked_relocations = set()
        checked_shapes = []
        prefix, tail, fall, taken = [],[],[],[]
        phases = {"prefix":prefix,"tail":tail,"continuationFall":fall,"continuationTaken":taken}
        for packet in fixture["packets"]:
            position = symbols[packet["label"]]
            expected = bytearray(packet["header"])
            headers.append((position,position+len(packet["header"])))
            local_relocations = {}
            for payload in packet["payloads"]:
                assert payload["offset"] == len(expected)
                word = value_of(payload["value"], symbols) % (1 << (8*payload["width"]))
                if payload["relocation"]:
                    assert payload["width"] == 4
                    expected.extend(encoded_address(word,position+payload["offset"],targets,section))
                else:
                    expected.extend(word.to_bytes(payload["width"],"little"))
                if payload["relocation"]:
                    local_relocations[payload["offset"]] = payload["relocation"]
                    checked_relocations.add(position+payload["offset"])
            assert len(expected) == packet["length"]
            actual = code[position:position+len(expected)]
            assert actual == expected, (fixture["name"],packet["source"],actual.hex(),expected.hex())
            canonical = bytearray(actual)
            for payload in packet["payloads"]:
                if payload["width"] == 4:
                    canonical[payload["offset"]:payload["offset"]+4] = bytes(4)
            assert tuple(canonical) in canonical_shapes, (packet["source"],canonical.hex())
            shape = canonical_shapes[tuple(canonical)]
            assert shape["length"] == len(actual)
            assert shape["address_offset"] == packet["payloads"][0]["offset"]
            variable_immediates = [payload for payload in packet["payloads"][1:] if payload["width"]==4]
            assert shape["immediate_offset"] == (variable_immediates[0]["offset"] if variable_immediates else 0)
            shape_name = shape["name"]
            observed_shapes.add(shape_name)
            checked_shapes.append(shape_name)
            actual_relocations = {offset-position:kind for offset,kind in relocations.items()
                                  if position <= offset < position+len(expected)}
            assert actual_relocations == local_relocations, (packet["source"],actual_relocations,local_relocations)
            destination = symbols[packet["writes"][0]]+packet["writes"][1]
            assert destination in fields.values(), "Write outside real owner field"
            phases[packet["phase"]].append((position,len(expected)))
        # These actual MOV storage owners include the address/return-slot alias.
        owners = [(labels["X"],symbols[labels["X"]]+6,False),
                  (labels["Y"],symbols[labels["Y"]]+6,False),
                  (labels["Stack"],symbols[labels["Stack"]]+6,True)]
        for symbol,field,stack_owner in owners:
            position = symbols[symbol]
            headers.append((position,position+2))
            expected = b"\xc7\x05"+encoded_address(field,position+2,targets,section)
            expected += encoded_address(field,position+6,targets,section) if stack_owner else bytes(4)
            assert code[position:position+10] == expected
            canonical = code[position:position+2]+bytes(8)
            assert canonical_shapes[tuple(canonical)]["name"] == "store"
            assert canonical_shapes[tuple(canonical)]["address_offset"] == 2
            assert canonical_shapes[tuple(canonical)]["immediate_offset"] == 6
            observed_shapes.add("store")
            checked_shapes.append("store")
            assert relocations.get(position+2) == 6
            assert relocations.get(position+6) == (6 if stack_owner else None)
            checked_relocations.add(position+2)
            if stack_owner:
                checked_relocations.add(position+6)
        assert all(finish <= head_start or head_end <= start
                   for start,finish,_ in intervals for head_start,head_end in headers), "Field overlaps opcode/ModR/M"
        gt, not_flag = fixture["gt"],fixture["not_flag"]
        assert len(prefix) == 10+4*fixture["signed"]+2*(not gt)+(not not_flag)
        assert len(tail) == 2 and len(fall) == len(taken) == 5
        for packets in [prefix+tail,fall,taken]:
            assert all(first[0]+first[1] == second[0] for first,second in zip(packets,packets[1:])), "Hidden gap in pure path"
        assert prefix[0][0] == symbols[labels["Start"]]
        assert tail[-1][0]+tail[-1][1] == symbols[labels["Fall"]]
        assert fall[0][0] == symbols[labels["Fall"]] and taken[0][0] == symbols[labels["Taken"]]
        assert fall[-1][0]+fall[-1][1] == symbols[labels["FallEnd"]]
        assert taken[-1][0]+taken[-1][1] == symbols[labels["TakenEnd"]]
        assert sum(length for _,length in fall) == sum(length for _,length in taken) == 30
        reference = reference_layouts[(fixture["signed"],fixture["relation"])]
        prefix_packets = [packet for packet in fixture["packets"] if packet["phase"]=="prefix"]
        assert len(reference["prefix"]) == len(prefix_packets)
        for index,(packet,formal) in enumerate(zip(prefix_packets,reference["prefix"])):
            position = symbols[packet["label"]]
            actual = bytearray(code[position:position+packet["length"]])
            expected = bytearray(formal["bytes"])
            assert len(actual) == len(expected) == packet["length"]
            assert packet["payloads"][0]["offset"] == 2
            actual[2:6] = expected[2:6] = bytes(4)
            destination = symbols[packet["writes"][0]]+packet["writes"][1]
            role = next(name for name,field in fields.items() if field==destination)
            assert role == formal["destination"], "Prefix differs from Lean field role"
            relocation = len(packet["payloads"])==2 and isinstance(packet["payloads"][1]["value"],dict)
            assert formal["relocation_immediate"] == relocation
            if relocation:
                assert index==len(prefix_packets)-3 and role=="delta"
                actual[6:10] = expected[6:10] = bytes(4)
            assert actual == expected, (fixture["name"],index,"Prefix differs from Lean emitter",actual.hex(),expected.hex())
        start = symbols[labels["Start"]]
        assert reference["prefix_bytes"] == sum(length for _,length in prefix)
        assert reference["and_offset"] == symbols[labels["Delta"]]-start
        assert reference["xor_offset"] == symbols[labels["Mask"]]-start
        assert reference["call_offset"] == symbols[labels["Call"]]-start
        assert reference["fall_offset"] == symbols[labels["Fall"]]-start
        for role,offset in reference["field_offsets"].items():
            assert fields[role]-start == offset, "Own-immediate/rel32 offset differs from Lean"
        assert reference["tail_bytes"]==11 and reference["continuation_bytes"]==30
        formal = spaced_layouts[(fixture["signed"],fixture["relation"])]
        assert formal["valid"] and len(formal["admissible_checks"])==10 and all(formal["admissible_checks"])
        assert formal["fields"] == fields
        assert formal["sites"] == {"signed":fixture["signed"],"relation":fixture["relation"],
            "stack":symbols[labels["Stack"]],"start":start,"taken":symbols[labels["Taken"]],"data":symbols[labels["X"]]}
        assert symbols[labels["Y"]] == symbols[labels["X"]]+10
        assert formal["fall"] == symbols[labels["Fall"]]
        assert formal["fall_end"] == symbols[labels["FallEnd"]]
        assert formal["taken_end"] == symbols[labels["TakenEnd"]]
        assert formal["image_end"] == symbols[labels["X"]]+20
        assert formal["delta"] == (symbols[labels["Taken"]]-symbols[labels["Fall"]]) % (1 << 32)
        assert formal["backward"] == (symbols[labels["Taken"]]<symbols[labels["Fall"]])
        pure = {symbols[packet["label"]]:packet for packet in fixture["packets"]}
        for role in ["Stack","X","Y"]:
            pure[symbols[labels[role]]] = {"writes":[labels[role],6]}
        assert len(formal["packets"]) == len(pure) == len(headers)
        assert len({packet["pc"] for packet in formal["packets"]}) == len(pure)
        for packet in formal["packets"]:
            position = packet["pc"]
            assert position in pure
            expected = bytearray(packet["bytes"])
            actual = bytearray(code[position:position+len(expected)])
            for offset in packet["absolute_offsets"]:
                assert relocations.get(position+offset) == 6
                actual[offset:offset+4] = expected[offset:offset+4] = bytes(4)
            assert actual == expected, (fixture["name"],position,"Spaced Lean packet differs",actual.hex(),expected.hex())
            source = pure[position]
            destination = symbols[source["writes"][0]]+source["writes"][1]
            role = next(name for name,field in fields.items() if field==destination)
            assert role == packet["destination"]
            assert packet["owned"] == sorted(field for field in fields.values() if position <= field and field+4 <= position+len(expected))
        results.append({"name":fixture["name"],"signed":fixture["signed"],"relation":fixture["relation"],
                        "prefix_instructions":len(prefix),"tail_instructions":2,"continuation_instructions":5,
                        "prefix_bytes":sum(length for _,length in prefix),"tail_bytes":11,"continuation_bytes":30,
                        "fields":fields,"owner_fields":7,"instruction_headers":len(headers),
                        "checked_relocations":len(checked_relocations),"lean_shape_names":checked_shapes,
                        "lean_prefix_checked":True,"lean_prefix_packets":len(prefix_packets),
                        "lean_own_offsets":reference["field_offsets"],
                        "lean_spaced_checked":True,"lean_spaced_packets":len(formal["packets"]),
                        "spaced_sites":formal["sites"],"spaced_gaps":formal["gaps"],
                        "relocation_delta":symbols[labels["Taken"]]-symbols[labels["Fall"]],
                        "taken_entry":symbols[labels["Taken"]],"fall_entry":symbols[labels["Fall"]]})
    assert observed_shapes == {shape["name"] for shape in shapes}
    return results


def main():
    folder = ROOT/"validation/.build/branch"
    fixtures = generate(folder)
    environment = vc_environment("x86")
    def tool(name):
        path = shutil.which(name,path=environment["PATH"])
        assert path, "Missing "+name
        return path
    commands = [[tool("ml.exe"),"/nologo","/c","/safeseh","/Fo"+str(folder/"branch.obj"),
                 "/Fl"+str(folder/"branch.lst"),str(folder/"branch.asm")],
                [tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/c",
                 "/I"+str(folder),str(ROOT/"validation/branch_native.cpp"),"/Fo"+str(folder/"harness.obj")],
                [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/OUT:"+str(folder/"branch.exe"),
                 str(folder/"harness.obj"),str(folder/"branch.obj")]]
    build = "".join(run(command,folder,environment) for command in commands)
    (folder/"build.log").write_text(build,encoding="utf-8")
    project = ROOT/"lean"
    toolchain = (project/"lean-toolchain").read_text().strip()
    binary = project/".elan/toolchains"/toolchain.replace("/","--").replace(":","---")/"bin"
    export_environment = dict(environment)
    export_environment["PATH"] = str(binary)+os.pathsep+export_environment["PATH"]
    exported = run(lean_command(project,binary,["ExportBranchEncoding.lean"]),project,export_environment)
    shapes = json.loads(exported)
    assert len(shapes) == 13
    (folder/"shapes.json").write_text(json.dumps(shapes,indent=2)+"\n",encoding="utf-8")
    layout_exported = run(lean_command(project,binary,["ExportBranchLayout.lean"]),project,export_environment)
    layouts = json.loads(layout_exported)
    assert len(layouts) == 12
    (folder/"layouts.json").write_text(json.dumps(layouts,indent=2)+"\n",encoding="utf-8")
    _,symbols,_ = coff(folder/"branch.obj","x86")
    sites = [{"signed":fixture["signed"],"relation":fixture["relation"],
              "stack":symbols[fixture["labels"]["Stack"]],"start":symbols[fixture["labels"]["Start"]],
              "taken":symbols[fixture["labels"]["Taken"]],"data":symbols[fixture["labels"]["X"]]} for fixture in fixtures]
    (folder/"sites.json").write_text(json.dumps(sites,indent=2)+"\n",encoding="utf-8")
    spaced_environment = dict(export_environment)
    spaced_environment["SMCTURING_BRANCH_SITES"] = str(folder/"sites.json")
    spaced_exported = run(lean_command(project,binary,["ExportBranchSpaced.lean"]),project,spaced_environment)
    spaced = json.loads(spaced_exported)
    assert len(spaced) == 12
    (folder/"spaced.json").write_text(json.dumps(spaced,indent=2)+"\n",encoding="utf-8")
    assembler_results = inspect(folder, fixtures, shapes, layouts, spaced)
    output = run([str(folder/"branch.exe")],folder,environment)
    (folder/"run.log").write_text(output,encoding="utf-8")
    rows = re.findall(r"^BRANCH (Branch[US](?:lt|le|eq|ne|gt|ge)): PASS (\d+) cases, (\d+) taken, (\d+) fallthrough$",output,re.M)
    assert [row[0] for row in rows] == [fixture["name"] for fixture in fixtures]
    cases = []
    for name,count,taken,fall in rows:
        count,taken,fall = int(count),int(taken),int(fall)
        assert count == taken+fall == 6200 and taken > 0 and fall > 0
        cases.append({"name":name,"passed":True,"cases":count,"taken":taken,"fallthrough":fall})
    assert "BRANCH x86: PASS 74400 cases" in output
    lean = json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"))
    assert lean["passed"] and lean["appendix_branch_tail_checked"] and lean["appendix_byte_code_checked"]
    assert lean["appendix_byte_execution_checked"] and lean["appendix_field_refinement_checked"] and lean["appendix_branch_execution_checked"]
    assert all(lean["appendix_"+stem+"_checked"] for stem in
               ["byte_image","byte_packing","byte_program","branch_layout","branch_prefix","byte_control","byte_linear","branch_control","branch_paths","branch_whole","byte_regions","spaced_layout","spaced_prefix","spaced_control","spaced_paths","spaced_whole"])
    proof_names = ["lean/SmcTuring/Appendix/"+name+".lean" for name in
                   ["Machine32","BranchAlgebra","Branching","BranchTail","ByteCode","ByteExecution","FieldRefinement","BranchExecution","ByteImage","BytePacking","ByteProgram","BranchLayout","BranchPrefix","ByteControl","ByteLinear","BranchControl","BranchPaths","BranchWhole","ByteRegions","SpacedLayout","SpacedPrefix","SpacedControl","SpacedPaths","SpacedWhole"]]
    proof_names += ["lean/ExportBranchEncoding.lean","lean/ExportBranchLayout.lean","lean/ExportBranchSpaced.lean"]
    pinned = {name.replace("\\","/"):expected for name,expected in lean["sources"].items()}
    for name in proof_names:
        assert digest(ROOT/name) == pinned[name], "Stale branch proof"
    source_names = ["validation/generate_branch.py","validation/branch_native.cpp","validation/run_branch.py",
                    "validation/audit_encoding.py","validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',
                    "lean/lakefile.proof.toml","validation/.cache/morse-2018.pdf"]+proof_names
    sources = {name:digest(ROOT/name) for name in source_names}
    assert sources["validation/.cache/morse-2018.pdf"] == PAPER_SHA256
    artifact_names = ["branch.asm","branch.hpp","manifest.json","branch.obj","branch.lst","harness.obj",
                      "branch.exe","build.log","run.log","shapes.json","layouts.json","sites.json","spaced.json"]
    report = {"as_of":date.today().isoformat(),"passed":True,"architecture":"x86",
              "coff_reference":"https://learn.microsoft.com/en-us/windows/win32/debug/pe-format",
              "published_listings":[4,10],"normalizations":["M05 independent target", "explicit DWORD field types", "forced imm32 owners"],
              "scope":"Finite MASM whole-branch regression; Lean branch has constructed live-byte trace at independent ordered block coordinates; physical ISA refinement open",
              "execution_environment":"Single thread, writable executable code, host FlushInstructionCache, CET shadow stacks disabled",
              "observations":["branch endpoint","all 8 GPRs including ESP/EBP","CF","all 7 owner words","all code bytes outside 3 final scratch fields"],
              "cases":74400,"edge_cases_per_variant":1200,"random_cases_per_variant":5000,
              "rng_seed":"0x4d6f7273652018","initial_CF":[0,1],"sources":sources,"commands":commands,
              "lean_audit_sha256":digest(ROOT/"validation/lean.json"),
              "artifacts":{str((folder/name).relative_to(ROOT)):digest(folder/name) for name in artifact_names},
              "assembler":assembler_results,"lean_shapes":shapes,"lean_layouts":layouts,"lean_spaced":spaced,"runs":cases,"output":output}
    (ROOT/"validation/branch.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(output.strip(),flush=True)
    print("Branch MASM: PASS 12 layouts, "+str(sum(item["instruction_headers"] for item in assembler_results))+
          " headers, "+str(sum(item["owner_fields"] for item in assembler_results))+" owned fields",flush=True)


if __name__ == "__main__":
    main()
