"""Emit the normalized printed x86 branch and literal code-backed continuation.

M05 supplies a separate target; DWORD types and imm32 owners are explicit.
Host setup/observation and inactive storage owners are outside the pure paths.
The generated packet manifest is finite assembler evidence, not a Lean proof.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
RELATIONS = ["lt", "le", "eq", "ne", "gt", "ge"]


def generate(folder: Path):
    lines = [".686", ".model flat, C", "option casemap:none", ".data"]
    fixtures = []
    declarations = []
    entries = []
    for signed in [False, True]:
        for relation in RELATIONS:
            stem = "Branch" + ("S" if signed else "U") + relation
            lines += ["PUBLIC " + stem + "Observation", stem + "Observation DWORD 12 DUP(0)"]
    lines += [".code"]
    for signed in [False, True]:
        for relation in RELATIONS:
            stem = "Branch" + ("S" if signed else "U") + relation
            labels = {role: stem + role for role in
                      ["X", "Y", "Mask", "Delta", "Call", "Stack", "Start", "Fall", "Taken",
                       "FallEnd", "TakenEnd", "ImageEnd", "Capture", "Clear", "Observation"]}
            gt = relation not in ["eq", "ne"]
            not_flag = relation not in ["le", "eq", "ge"]
            swap = relation in ["lt", "ge"]
            x, y = (labels["Y"], labels["X"]) if swap else (labels["X"], labels["Y"])
            x, y = (x, 6), (y, 6)
            mask, delta, displacement = (labels["Mask"], 6), (labels["Delta"], 6), (labels["Call"], 1)
            pointer, address = (labels["Stack"], 6), (labels["Stack"], 2)
            packets = []
            publics = [stem] + [labels[role] for role in labels if role != "Observation"]
            lines += ["PUBLIC " + ", ".join(publics),
                      stem + " PROC uses ebx esi edi seed:DWORD, initialCarry:DWORD",
                      # Host setup is outside Start/Fall/Taken packet intervals.
                      labels["Stack"] + "::",
                      "    mov dword ptr [" + labels["Stack"] + "+6], OFFSET " + labels["Stack"] + "+6",
                      "    mov dword ptr [" + labels["Observation"] + "+36], esp",
                      "    mov dword ptr [" + labels["Observation"] + "+40], ebp",
                      "    mov ebx, 13579bdfh", "    mov ecx, 2468ace0h", "    mov edx, 0badc0deh",
                      "    mov esi, 11223344h", "    mov edi, 55667788h", "    mov eax, seed",
                      "    cmp initialCarry, 0", "    je " + labels["Clear"], "    stc",
                      "    jmp " + labels["Start"], labels["Clear"] + "::", "    clc"]

            def operand(field):
                return field[0] + ("+" + str(field[1]) if field[1] else "")

            def emit(source, header, destination, immediate=None, imm_width=0, role=None, phase="prefix"):
                name = stem + "P" + str(len(packets))
                if role:
                    lines.append(labels[role] + "::")
                lines.extend(["PUBLIC " + name, name + "::", "    " + source])
                payloads = [{"offset": len(header), "width": 4,
                             "value": {"symbol": destination[0], "add": destination[1]},
                             "relocation": 6}]
                if imm_width:
                    payloads.append({"offset": len(header) + 4, "width": imm_width,
                                     "value": immediate, "relocation": 0})
                packets.append({"label": name, "source": source, "header": header,
                                "length": len(header) + 4 + imm_width, "payloads": payloads,
                                "writes": list(destination), "phase": phase})

            def store(field, value):
                text = value if isinstance(value, str) else str(value)
                emit("mov dword ptr [" + operand(field) + "], " + text, [0xc7, 0x05],
                     field, value, 4)

            def unary(op, field):
                emit(op + " dword ptr [" + operand(field) + "]",
                     [0xf7, 0x1d if op == "neg" else 0x15], field)

            def exchange(field, phase="prefix"):
                emit("xchg dword ptr [" + operand(field) + "], eax", [0x87, 0x05], field, phase=phase)

            def flip(field):
                emit("xor dword ptr [" + operand(field) + "], 80000000h", [0x81, 0x35],
                     field, 0x80000000, 4)

            lines.append(labels["Start"] + "::")
            store(displacement, 0)
            store(mask, 0)
            if signed:
                flip(x)
            exchange(x)
            if signed:
                flip(y)
            emit("sub dword ptr [" + operand(y) + "], eax", [0x29, 0x05], y)
            if not gt:
                unary("neg", y)
            emit("sbb dword ptr [" + operand(mask) + "], 0", [0x83, 0x1d], mask, 0, 1)
            if not gt:
                unary("neg", y)
            emit("add dword ptr [" + operand(y) + "], eax", [0x01, 0x05], y)
            if signed:
                flip(y)
            exchange(x)
            if signed:
                flip(x)
            if not not_flag:
                unary("not", mask)
            relocation = {"difference": [labels["Taken"], labels["Call"]], "add": -5}
            store(delta, labels["Taken"] + "-" + labels["Call"] + "-5")
            packets[-1]["payloads"][-1]["value"] = relocation
            emit("and dword ptr [" + operand(mask) + "], 80000000h", [0x81, 0x25], mask,
                 0x80000000, 4, role="Delta")
            emit("xor dword ptr [" + operand(displacement) + "], 80000000h", [0x81, 0x35], displacement,
                 0x80000000, 4, role="Mask")
            emit("xchg dword ptr [" + operand(pointer) + "], esp", [0x87, 0x25], pointer, phase="tail")
            name = stem + "P" + str(len(packets))
            lines += [labels["Call"] + "::", "PUBLIC " + name, name + "::",
                      "    call [" + labels["Call"] + "+5]"]
            packets.append({"label": name, "source": "call [" + labels["Call"] + "+5]",
                            "header": [0xe8], "length": 5,
                            "payloads": [{"offset": 1, "width": 4, "value": 0, "relocation": 0}],
                            "writes": list(address), "phase": "tail"})
            for role, outcome in [("Fall", 0), ("Taken", 1)]:
                lines.append(labels[role] + "::")
                phase = "continuation" + role
                emit("xchg dword ptr [" + operand(pointer) + "], esp", [0x87, 0x25], pointer, phase=phase)
                emit("add dword ptr [" + operand(pointer) + "], 4", [0x83, 0x05], pointer, 4, 1, phase=phase)
                exchange(pointer, phase)
                emit("mov dword ptr [" + operand(address) + "], eax", [0xa3], address, phase=phase)
                exchange(pointer, phase)
                lines += [labels[role + "End"] + "::",
                          "    mov dword ptr [" + labels["Observation"] + "+44], " + str(outcome),
                          "    jmp " + labels["Capture"]]
            lines.append(labels["Capture"] + "::")
            for index, register in enumerate(["eax", "esp", "ebx", "ecx", "edx", "esi", "edi", "ebp"]):
                lines.append("    mov dword ptr [" + labels["Observation"] + "+" + str(4*index) + "], " + register)
            lines += ["    pushfd", "    pop eax", "    mov dword ptr [" + labels["Observation"] + "+32], eax",
                      "    mov eax, dword ptr [" + labels["Observation"] + "+44]", "    ret", stem + " ENDP"]
            for role in ["X", "Y"]:
                lines += [labels[role] + ":", "    mov dword ptr [" + labels[role] + "+6], 0"]
            lines.append(labels["ImageEnd"] + ":")
            fields = {"x": [labels["X"], 6], "y": [labels["Y"], 6], "mask": list(mask),
                      "delta": list(delta), "displacement": list(displacement),
                      "pointer": list(pointer), "address": list(address)}
            fixtures.append({"name": stem, "signed": signed, "relation": relation, "gt": gt,
                             "not_flag": not_flag, "swap": swap, "labels": labels,
                             "fields": fields, "packets": packets})
            declarations += [f'extern "C" std::uint32_t __cdecl {stem}(std::uint32_t, std::uint32_t);',
                             f'extern "C" Observation {labels["Observation"]};']
            declarations += ['extern "C" unsigned char ' + labels[role] + '[];' for role in
                             ["X", "Y", "Mask", "Delta", "Call", "Stack", "Start", "Fall", "Taken", "ImageEnd"]]
            entries.append('{"' + stem + '", ' + stem + ', ' + str(signed).lower() + ', Relation::' + relation +
                           ', ' + ', '.join(labels[role] for role in ["X", "Y", "Mask", "Delta", "Call", "Stack", "Fall", "Taken", "ImageEnd"]) +
                           ', &' + labels["Observation"] + '}')
    lines += ["END"]
    folder.mkdir(parents=True, exist_ok=True)
    (folder/"branch.asm").write_text("\n".join(lines)+"\n", encoding="utf-8")
    (folder/"branch.hpp").write_text("\n".join(declarations)+
                                   "\nstatic const Fixture fixtures[] = {\n"+
                                   ",\n".join(entries)+"\n};\n", encoding="utf-8")
    (folder/"manifest.json").write_text(json.dumps(fixtures, indent=2)+"\n", encoding="utf-8")
    return fixtures


if __name__ == "__main__":
    generate(ROOT/"validation/.build/branch")
