"""Compare the finite MASM fixtures with instruction shapes exported by Lean.

This checks assembler output and COFF relocation placement; it does not prove
CPU execution semantics or hardware instruction-fetch coherence.
"""
from __future__ import annotations

from collections import Counter
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
from lean_export import lean_command

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean"
COFF_REFERENCE = "https://learn.microsoft.com/en-us/windows/win32/debug/pe-format"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coff(path: Path, architecture: str):
    data = path.read_bytes()
    machine, count, _, symbol_start, symbol_count, optional_size, _ = struct.unpack_from("<HHIIIHH", data)
    assert machine == {"x86": 0x14C, "x64": 0x8664}[architecture]
    sections = [struct.unpack_from("<8sIIIIIIHHI", data, 20 + optional_size + 40 * index)
                for index in range(count)]
    selected = [index for index, section in enumerate(sections)
                if section[0].rstrip(b"\0") == b".text$mn"]
    assert len(selected) == 1
    section_index = selected[0] + 1
    section = sections[selected[0]]
    assert section[9] & 0x20, "Expected executable instruction section"
    code = data[section[4]:section[4] + section[3]]
    strings = symbol_start + symbol_count * 18
    symbols = {}
    valid_symbol_indices = set()
    index = 0
    while index < symbol_count:
        name_bytes, value, number, _, _, auxiliary = struct.unpack_from("<8sIhHBB", data, symbol_start + index * 18)
        if name_bytes[:4] == b"\0" * 4:
            start = strings + struct.unpack_from("<I", name_bytes, 4)[0]
            name = data[start:data.index(b"\0", start)].decode("ascii")
        else:
            name = name_bytes.rstrip(b"\0").decode("ascii")
        if architecture == "x86" and name.startswith("_"):
            name = name[1:]
        if number == section_index:
            assert name not in symbols
            symbols[name] = value
        valid_symbol_indices.add(index)
        index += 1 + auxiliary
    relocations = {}
    assert section[7] < 65535, "COFF extended relocation counts are outside this fixture"
    for index in range(section[7]):
        position, symbol, kind = struct.unpack_from("<IIH", data, section[5] + 10 * index)
        assert symbol in valid_symbol_indices and position not in relocations
        assert position < len(code)
        relocations[position] = kind
    return code, symbols, relocations


def listing_rows(path: Path):
    rows = []
    labels = {}
    in_code = False
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if "\t" not in line:
            continue
        source = re.split(r"\t+", line)[-1].strip()
        if source.lower() in {".code", ".data"}:
            in_code = source.lower() == ".code"
            continue
        address = re.match(r"^\s*([0-9A-F]{8})\b", line)
        if not in_code or not address:
            continue
        if not re.match(r"^[A-Za-z]", source):
            continue
        position = int(address.group(1), 16)
        if source.endswith(":"):
            labels[source[:-1]] = position
        rows.append((position, source))
    return rows, labels


def classify(source: str, architecture: str) -> str:
    operation, arguments = source.split(None, 1)
    operation = operation.lower()
    arguments = arguments.lower()
    accumulator, stack = ("rax", "rsp") if architecture == "x64" else ("eax", "esp")
    if operation == "xchg":
        first = arguments.split(",")[0].strip()
        if first == stack:
            return "exchangeStack"
        assert first == accumulator, source
        return "exchangeIndirect" if "[" + accumulator + "]" in arguments else "exchangeAcc"
    if operation == "mov":
        destination, value = [part.strip() for part in arguments.split(",")]
        assert "[" in destination, source
        if value == stack:
            return "storeStack"
        assert value == accumulator, source
        return "storeAcc" if architecture == "x64" else "moffs"
    if operation == "call":
        return "callIndirect" if "[" in arguments else "callRelative"
    names = {"add": "add", "sub": "subtract", "xor": "bitXor", "and": "bitAnd",
             "sbb": "subtractBorrowZero"}
    assert operation in names, "Instruction outside the selected codec: " + source
    assert "[" in arguments, source
    value = arguments.rsplit(",", 1)[-1].strip()
    assert value == ("0" if operation == "sbb" else accumulator), source
    return names[operation]


def check_shape(code: bytes, position: int, shape: dict):
    expected = shape["bytes"]
    assert len(expected) == shape["length"] <= 15
    start, width = shape["payload_offset"], shape["payload_width"]
    actual = code[position:position + len(expected)]
    assert len(actual) == len(expected)
    assert all(byte == expected[index] for index, byte in enumerate(actual)
               if not start <= index < start + width), (position, shape["name"], actual.hex())


def check_skipped_padding(data: bytes, architecture: str):
    # These ALIGN bytes sit between called entries. They are excluded from the
    # selected computational forms; CPU refinement must prove they are skipped.
    alignment = [b"\x8b\xff"] if architecture == "x86" else [
        b"\x0f\x1f\x40\x00", b"\x0f\x1f\x80\x00\x00\x00\x00"]
    assert all(byte == 0x90 for byte in data) or any(
        data.startswith(leading) and all(byte == 0x90 for byte in data[len(leading):])
        for leading in alignment), (architecture, "Unclassified padding", data.hex())


def audit_architecture(architecture: str, shapes: dict, checked_layout: dict):
    directory = ROOT / "validation/.build/pure" / architecture
    code, symbols, relocations = coff(directory / "pure.obj", architecture)
    rows, labels = listing_rows(directory / "pure.lst")
    layout = json.loads((directory / "layout.json").read_text(encoding="utf-8"))
    assert layout["architecture"] == architecture
    width, stride = layout["word_bytes"], layout["stride"]
    assert width == shapes["moffs"]["payload_width"] and stride == 2 * width
    begin, end = labels["Read_R0"], symbols["PureBoundary"]
    # Compare independently emitted MASM positions with the kernel-checked
    # two-pass allocator. Host-stub geometry is explicit input, verified here.
    assert checked_layout["architecture"] == architecture
    entry_ends = [position for position, source in rows if source == "PureNativeEntry ENDP"]
    host_returns = [position for position, source in rows
                    if end <= position < symbols["StackTop"] and source.lower() == "ret"]
    assert entry_ends == [checked_layout["origin"]] and len(host_returns) == 2
    assert code[max(host_returns)] == 0xC3
    assert max(host_returns) + 1 - end == checked_layout["host_span"]
    assert symbols["PureFault"] - end == checked_layout["terminal_offset"]
    assert 0 <= checked_layout["terminal_offset"] < checked_layout["host_span"], "Terminal endpoint outside host span"
    assert layout["heap_cells"] == checked_layout["cells"]
    for key, name in [("base_guard", "Guard_Base"), ("offset_guard", "Guard_Offset"),
                      ("kernel", "PureKernelStart"), ("boundary", "PureBoundary"),
                      ("terminal", "PureFault"), ("grid", "PureRegisters"), ("heap", "PureHeap")]:
        assert labels.get(name, symbols.get(name)) == checked_layout[key], (architecture, key)
    assert len(checked_layout["readers"]) == 23 and len(checked_layout["fields"]) == 13
    for reader in checked_layout["readers"]:
        assert labels["Read_" + reader["name"]] == reader["entry"]
        label = "PointerLabel" if reader["name"] == "Pointer" else "Label_" + reader["name"]
        assert symbols[label] == reader["operand"]
    for field in checked_layout["fields"]:
        assert symbols[field["name"]] == field["operand"]
    positions = checked_layout["source_positions"]
    assert len(positions) == 64
    assert positions == [labels["Source_" + str(index)] for index in range(64)]
    # The final three computational headers are the actual reset/backedge.
    backedge_rows = [(position, source) for position, source in rows
                     if checked_layout["backedge"] <= position < end]
    assert len(backedge_rows) == 3 and backedge_rows[0][0] == checked_layout["backedge"]
    assert backedge_rows[-1][1].endswith("[PureLoopTarget]")
    for sense, key in [("Base", "base_guard"), ("Offset", "offset_guard")]:
        assert symbols["Label_Capture_" + sense] == checked_layout[key] + (19 if architecture == "x64" else 14)
    fields, active_headers = [], set()
    for name, owner in layout["owners"].items():
        assert owner["instruction"] == "MOV_MOFFS"
        count = owner.get("fields", 1)
        spacing = owner.get("stride", stride)
        assert count > 0 and spacing == stride
        for index in range(count):
            field = symbols[name] + index * spacing
            position = field - shapes["moffs"]["payload_offset"]
            assert field % width == 0 and position >= 0
            check_shape(code, position, shapes["moffs"])
            fields.append(field)
            if owner["active"]:
                assert begin <= position < end and position not in active_headers
                active_headers.add(position)
    fields.sort()
    assert len(set(fields)) == len(fields)
    assert all(first + width <= second - shapes["moffs"]["payload_offset"]
               for first, second in zip(fields, fields[1:]))
    assert symbols["PureHeap"] == symbols["PureRegisters"] + 13 * stride
    assert layout["owners"]["PureRegisters"]["fields"] == 13
    assert layout["owners"]["PureHeap"]["fields"] == 2 * layout["heap_cells"]
    headers = {position: ("moffs", "owned MOFFS") for position in active_headers}
    padding_count = 0
    for position, source in rows:
        if not begin <= position < end or source.endswith(":"):
            continue
        operation = source.split()[0].upper()
        if operation == "DB":
            padding = re.fullmatch(r"DB (\d+) DUP \(90h\)", source, re.I)
            if padding:
                count = int(padding.group(1))
                assert code[position:position + count] == b"\x90" * count
                padding_count += count
            else:
                assert position in active_headers, "Unclassified DB instruction: " + source
            continue
        if operation in {"DD", "DQ"} or (len(source.split()) >= 2 and source.split()[1].upper() in {"DD", "DQ"}):
            assert position in fields, "Unowned code data: " + source
            continue
        assert operation not in {"ALIGN", "DD", "DQ", "PROC", "ENDP"}, source
        name = classify(source, architecture)
        assert position not in headers
        check_shape(code, position, shapes[name])
        headers[position] = (name, source)
    counts, seen_relocations = Counter(), set()
    previous_end = begin
    skipped_padding = 0
    for position, (name, source) in sorted(headers.items()):
        shape = shapes[name]
        assert previous_end <= position
        check_skipped_padding(code[previous_end:position], architecture)
        skipped_padding += position - previous_end
        previous_end = position + shape["length"]
        assert previous_end <= end
        counts[name] += 1
        local = [(address, kind) for address, kind in relocations.items()
                 if position <= address < previous_end]
        payload = position + shape["payload_offset"]
        if name == "exchangeIndirect":
            assert not local
        elif name == "callRelative" and not local:
            target = re.fullmatch(r"(\w+)([+-]\d+)?", source.split()[-1])
            assert target is not None, source
            base, addend = target.group(1), int(target.group(2) or "0")
            assert base in labels or base in symbols, source
            destination = labels.get(base, symbols.get(base)) + addend
            assert destination in headers, "CALL does not target a selected instruction"
            displacement = int.from_bytes(code[payload:payload + 4], "little", signed=True)
            assert previous_end + displacement == destination
        else:
            expected_kind = (0x14 if name == "callRelative" else 0x6) if architecture == "x86" else (
                0x1 if name == "moffs" else 0x5 if name == "subtractBorrowZero" else 0x4)
            assert local == [(payload, expected_kind)], (architecture, position, name, local)
            seen_relocations.add(payload)
    assert seen_relocations == {address for address in relocations if begin <= address < end}
    check_skipped_padding(code[previous_end:end], architecture)
    skipped_padding += end - previous_end
    assert counts["subtractBorrowZero"] == 2 and counts["callRelative"] > 0
    assert active_headers <= set(headers)
    artifacts = {str((directory / name).relative_to(ROOT)): digest(directory / name)
                 for name in ["pure.obj", "pure.lst", "pure.asm", "layout.json"]}
    return {"architecture": architecture, "passed": True, "computational_interval": [begin, end],
            "instruction_headers": len(headers), "forms": dict(sorted(counts.items())),
            "owned_fields": len(fields), "active_moffs_owners": len(active_headers),
            "padding_bytes": skipped_padding, "literal_padding_bytes": padding_count,
            "code_relocations": len(seen_relocations),
            "coff_relocation_kinds": dict(sorted(Counter(relocations.values()).items())),
            "artifacts": artifacts, "computed_layout_checked": True, "host_endpoint_checked": True, "computed_layout": checked_layout}


def main():
    toolchain = (PROJECT / "lean-toolchain").read_text().strip()
    binary = PROJECT / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin"
    environment = dict(os.environ)
    environment["PATH"] = str(binary) + os.pathsep + environment["PATH"]
    export = subprocess.run(lean_command(PROJECT, binary,["ExportEncoding.lean"]),
                            cwd=PROJECT, env=environment, capture_output=True, text=True,
                            encoding="utf-8", check=True, timeout=120)
    shapes = json.loads(export.stdout)
    assert len(shapes) == 26
    layout_export = subprocess.run(lean_command(PROJECT, binary,["ExportLayout.lean"]),
                                   cwd=PROJECT, env=environment, capture_output=True, text=True,
                                   encoding="utf-8", check=True, timeout=120)
    checked_layouts = {item["architecture"]: item for item in json.loads(layout_export.stdout)}
    assert set(checked_layouts) == {"x86", "x64"}
    native = json.loads((ROOT / "validation/pure.json").read_text(encoding="utf-8"))
    assert native["lean_audit_sha256"] == digest(ROOT / "validation/lean.json")
    source_paths = ["validation/audit_encoding.py", "validation/generate_pure.py", "lean/ExportEncoding.lean",
                    "validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py', "lean/lakefile.proof.toml", "lean/ExportLayout.lean"]
    source_paths += [str(path.relative_to(ROOT)) for path in (PROJECT / "SmcTuring/Native").glob("*.lean")]
    report = {"as_of": date.today().isoformat(), "toolchain": toolchain, "coff_reference": COFF_REFERENCE,
              "lean_audit_sha256": digest(ROOT / "validation/lean.json"),
              "native_report_sha256": digest(ROOT / "validation/pure.json"),
              "sources": {name: digest(ROOT / name) for name in source_paths}, "shapes": shapes,
              "runs": [audit_architecture(architecture, {shape["name"]: shape for shape in shapes
                        if shape["architecture"] == architecture}, checked_layouts[architecture]) for architecture in ["x86", "x64"]],
              "passed": True}
    (ROOT / "validation/encoding.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    for run in report["runs"]:
        print(f"{run['architecture']}: {run['instruction_headers']} instruction headers, "
              f"{run['owned_fields']} owned fields, {run['code_relocations']} relocations checked")


if __name__ == "__main__":
    main()
