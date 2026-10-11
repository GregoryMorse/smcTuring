"""Check the compact errata against published excerpts and audited positive proofs.

The .diff is a location-annotated excerpt diff, not a patch to unavailable
publisher TeX. PDF text extraction normalizes whitespace and ligatures only.
"""
from pathlib import Path
from datetime import date
import argparse
import hashlib
import json
import re
import subprocess
import sys
import unicodedata

ROOT = Path(__file__).resolve().parents[1]
ERRATA = ROOT / "lean/errata"
OUTPUT = ROOT / "output/pdf/morse-2018-errata.pdf"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def normalized(text):
    return re.sub(r"\s+", " ", unicodedata.normalize("NFKC", text)).strip()

def make_diff(edits):
    lines = ["--- Published article excerpts (whitespace reflowed)",
             "+++ Corrected article excerpts (whitespace reflowed)"]
    for edit in edits:
        lines.append(f"@@ {edit['id']}: p.{edit['page']}, {edit['location']} @@")
        if edit["kind"] == "replace":
            lines.extend(["- " + edit["before"], "+ " + edit["after"]])
        elif edit["kind"] == "insert_after":
            lines.extend(["  " + edit["before"], "+ " + edit["after"]])
        elif edit["kind"] == "insert_before":
            lines.extend(["+ " + edit["after"], "  " + edit["before"]])
        else:
            raise AssertionError(edit["kind"])
    return "\n".join(lines) + "\n"

PROOFS = [
    *["SmcTuring.Appendix.Listing8CursorFields." + name for name in
      ["field_is_operand", "printed_x86_is_header", "x86_bare_label_counterexample", "x64_immediate_offset_counterexample", "source_cursor"]],
    *["SmcTuring.Appendix.Listing8PointerTargets." + name for name in
      ["slots", "opcode_copy_counterexample", "immediate_patch", "pointer_half_effect", "half_selected"]],
    *["SmcTuring.Appendix.Listing8Prototypes." + name for name in
      ["pointer_label_is_not_entry", "node_length", "node_values", "transition_length", "transition_values"]],
    *["SmcTuring.Appendix.Listing8PrototypeCopy." + name for name in
      ["node_copy", "transition_copy", "short_node_zero_counterexample", "operand_destination_counterexample", "end_labels"]],
    *["SmcTuring.Appendix.Listing8SourceEffects." + name for name in
      ["effect", "retained", "tape_value"]],
    "SmcTuring.Native.StringInitTrace.trace",
    *["SmcTuring.Appendix.Listing8LiteralComposition." + name for name in
      ["trace", "restored_mask_source", "destination_values"]],
    *["SmcTuring.Appendix.Listing8LiteralMaskTrace." + name for name in
      ["trace", "copies_valid", "x64_masks"]],
    *["SmcTuring.Appendix.Listing8MaskCopy." + name for name in [
        "printed_source_counterexample", "printed_source_is_not_zero_mask",
        "printed_source_is_not_true_mask", "instruction_start_not_mask", "mask_operand", "copy_mask_correct",
        "repeated_mask", "broadcast_correct"]],
    "SmcTuring.Appendix.DivisionAlgebra.scan_correct",
    "SmcTuring.Appendix.DivisionAlgebra.trial_fits",
    "SmcTuring.Appendix.DivisionAlgebra.full_word_division",
    "SmcTuring.Appendix.DivisionRepairs.divisor_copy",
    "SmcTuring.Appendix.DivisionRepairs.divisor_copy_register",
    "SmcTuring.Appendix.DivisionRepairs.exit_selection",
    "SmcTuring.Appendix.DivisionRepairs.exit_delta",
    "SmcTuring.Appendix.DivisionRepairs.body_continuation",
    "SmcTuring.Appendix.DivisionRepairs.reset_owned_field",
    "SmcTuring.Appendix.DivisionRepairs.reset_packet",
    "SmcTuring.Appendix.DivisionRepairs.reset_fetch",

    *["SmcTuring.Native.DwordOwner." + name for name in ["initial_zero", "patched_current", "correct", "pure"]],
    *["SmcTuring.Native.TerminalMarker." + name for name in ["correct", "pure", "reusable", "output_preserved"]],
    *["SmcTuring.Appendix.InputDword." + name for name in ["copy_correct", "copy_pure", "current_source_word", "source_code_frame"]],
    "SmcTuring.Appendix.InputOperand.patched_target",
    "SmcTuring.Native.StringPlan.correct",
    "SmcTuring.Native.StringPlan.literal_widths",
    "SmcTuring.Native.StringCursor.pair_correct",
    "SmcTuring.Native.StringFields.prepared_source",
    "SmcTuring.Native.StringFields.effect",
    "SmcTuring.Native.StringFields.frame",
    *["SmcTuring.Appendix.ZeroImage." + name for name in [
      "effect", "correct", "original_image_correct", "intact_after", "reentry_trace"]],
    "SmcTuring.Appendix.ConstantAlgebra.decomposition",
    "SmcTuring.Appendix.ConstantAlgebra.gap_invariant",
    "SmcTuring.Appendix.ConstantAlgebra.correct",
    "SmcTuring.Appendix.ConstantAlgebra.signed_low_product",
    "SmcTuring.Appendix.ConstantWords.contract",
    "SmcTuring.Appendix.ConstantWords.program_legal",
    "SmcTuring.Appendix.MultiplyByteCorrect.correct",
    "SmcTuring.Defaddr.corrected_effect",
    "SmcTuring.Defaddr.repair_equivalent",
    "SmcTuring.Defaddr.corrected_pure",
    "SmcTuring.Defaddr.repair32",
    "SmcTuring.Defaddr.repair64",
    "SmcTuring.Defaddr.arbitrary_repetitions_pure",
    "SmcTuring.Defaddr.arbitrary_repetitions_restore_memory",
    *["SmcTuring.X64.HalfWords." + name for name in
      ["pack_halves", "split_mov", "split_xor", "split_and", "split_or",
       "split_not", "broadcast_as_repeated", "add_carry", "sub_borrow",
       "split_add_no_carry", "split_sub_no_borrow", "repeated_masks"]],
    "SmcTuring.Appendix.Branching.relation_displacement",
    "SmcTuring.Appendix.Branching.relation_target",
    "SmcTuring.Appendix.Branching.relation_accumulator",
    "SmcTuring.Appendix.Branching.relation_frame",
    "SmcTuring.Appendix.Branching.relation_pure",
    "SmcTuring.Appendix.SpacedWhole.correct",
    "SmcTuring.Appendix.SpacedWhole.gap_frame",
    "SmcTuring.SMC.Concrete.pure_unbounded_smc_witness",
    "SmcTuring.X64.HalfFrame.split_effect",
    "SmcTuring.X64.HalfFrame.split_correct",
    "SmcTuring.X64.HalfFrame.split_pure",
    "SmcTuring.X64.HalfFrame.complement_correct",
    "SmcTuring.X64.HalfFrame.complement_registers",
    "SmcTuring.X64.HalfFrame.complement_pure",
    "SmcTuring.Appendix.MultiplyWords.guard_target",
    "SmcTuring.Appendix.MultiplyWords.body_field",
    "SmcTuring.Appendix.MultiplyAlgebra.step_invariant",
    "SmcTuring.Appendix.MultiplyAlgebra.full_word_product",
    "SmcTuring.Appendix.MultiplyLoop.full_product",
    "SmcTuring.Appendix.MultiplyLoop.multiply_pure",
    "SmcTuring.Appendix.MultiplyLoop.multiply_frame",
    "SmcTuring.Appendix.MultiplyLoop.multiply_length",
    'SmcTuring.Appendix.Listing9Fields.operand_field',
    'SmcTuring.Appendix.Listing9Fields.save_field',
    'SmcTuring.Appendix.Listing9Fields.pointer_field',
    'SmcTuring.Appendix.Listing9Fields.x86_header_not_operand',
    'SmcTuring.Appendix.Listing9Fields.corrected_pointer',
    'SmcTuring.Appendix.Listing9PackedLayout.admissible',
    'SmcTuring.Appendix.Listing9ExecutionImage.execute',
]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-diff", action="store_true")
    parser.add_argument("--remote-source-proof", action="store_true",
                        help="Check source edits, the current Linux proof audit and PDF only; no Windows/native aggregate claim")
    args = parser.parse_args()
    manifest = json.loads((ERRATA / "edits.json").read_text(encoding="utf-8"))
    source = ROOT / manifest["source"]
    assert digest(source) == manifest["source_sha256"]
    if args.remote_source_proof:
        extracted = subprocess.run(["pdftotext", str(source), "-"],
                                   capture_output=True, text=True, check=True).stdout
        pages = [normalized(page) for page in extracted.split("\f") if page.strip()]
        assert len(pages) == 7
    else:
        import fitz
        with fitz.open(source) as pdf:
            assert len(pdf) == 7
            pages = [normalized(page.get_text()) for page in pdf]
    edits = manifest["edits"]
    assert len(edits) == 60 and len({edit["id"] for edit in edits}) == 60
    for edit in edits:
        text = pages[edit["page"] - 123]
        assert normalized(edit["before"]) in text, edit["id"]
        assert edit["before"] != edit["after"], edit["id"]
        if "occurrence" in edit:
            listing = edit.get("listing", 11)
            block = text.split("Listing "+str(listing)+".",1)[1].split("Listing "+str(listing+1)+".",1)[0]
            assert block.count(normalized(edit["before"]))==2, edit["id"]
            assert edit["occurrence"] in [1,2], edit["id"]
    expected = make_diff(edits)
    diff = ERRATA / "morse-2018-minimal.diff"
    if args.write_diff:
        diff.write_text(expected, encoding="utf-8")
    assert diff.read_text(encoding="utf-8") == expected
    if args.remote_source_proof:
        sys.path.insert(0, str(ROOT / "validation/remote-agent"))
        from checkpoint_common import audit_gate
        audit = audit_gate()
        lean_path = ROOT / "validation/remote-evidence/lean.json"
    else:
        lean_path = ROOT / "validation/lean.json"
    lean = json.loads(lean_path.read_text(encoding="utf-8"))
    declarations = {item["name"]: item for item in lean["declarations"]}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in PROOFS:
        assert name in declarations, name
        assert set(declarations[name]["axioms"]) <= allowed, name
    if args.remote_source_proof:
        extracted = subprocess.run(["pdftotext", "-layout", str(OUTPUT), "-"],
                                   capture_output=True, text=True, check=True).stdout
        output_pages = [page for page in extracted.split("\f") if page.strip()]
        assert len(output_pages) == 2, "The compact errata must remain two pages."
        output_text = normalized(extracted)
        for number in range(1, 21):
            assert f"M{number:02d}." in output_text
        assert "Justification of the corrections" in output_text
        assert "10.24425/119359" in output_text
        tex = ERRATA / "morse-2018-errata.tex"
        log = ROOT / "output/pdf/morse-2018-errata.log"
        log_text = log.read_text(encoding="utf-8", errors="replace")
        assert "Overfull" not in log_text and "Undefined control sequence" not in log_text
        evidence = dict(passed=True, as_of=date.today().isoformat(),
                        scope="M01-M20 exact source excerpts, current Linux positive proofs and two-page PDF text; Windows/native aggregate remains separate",
                        source_excerpts_checked=len(edits), positive_proofs=PROOFS,
                        pages=2, native_windows_checked=False,
                        lean_report_sha256=audit["report_sha256"],
                        sources={str(path.relative_to(ROOT)).replace("\\", "/"): digest(path)
                                 for path in [Path(__file__), source, ERRATA / "edits.json", tex, diff]},
                        artifacts={str(path.relative_to(ROOT)).replace("\\", "/"): digest(path)
                                   for path in [OUTPUT, log]})
        target = ROOT / "validation/remote-evidence/errata-source-proof.json"
        target.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
        print(f"Remote errata source/proof/PDF: {len(edits)} exact excerpts; {len(PROOFS)} positive proof references; two pages; Windows/native aggregate remains separate")
        return
    repaired = (ROOT / "smcTuring/pure_smc.inc").read_text(encoding="utf-8")
    macro = repaired.split("DEFADDR MACRO", 1)[1].split("ENDM", 1)[0]
    assert "xchg SMC_ACC, SMC_WORD ptr [SMC_ACC]" in macro
    assert "mov SMC_ACC, SMC_WORD ptr [SMC_ACC]" not in macro
    zero = (ROOT / "smcTuring/listing6_smc.inc").read_text(encoding="utf-8")
    assert "labelname: xor DWORD PTR [labelname+6],80000000h" in zero
    division = json.loads((ROOT / "validation/division.json").read_text(encoding="utf-8"))
    assert division["passed"] and division["executions"]==52648
    assert division["lean_audit_sha256"]==digest(ROOT / "validation/lean.json")
    assert division["whole_literal_execution_proof"]
    division_proofs = ["SmcTuring.Appendix.DivisionByteCorrect." + name for name in
                       ["correct", "reusable_correct", "signed_quotient", "signed_remainder",
                        "unsigned_quotient", "unsigned_remainder"]]
    assert set(division_proofs) <= set(division["byte_execution_proofs"])
    assert all(set(declarations[name]["axioms"]) <= allowed for name in division_proofs)
    terminal = json.loads((ROOT / "validation/terminal.json").read_text(encoding="utf-8"))
    assert terminal["passed"] and terminal["actual_lean_codec_checked"] and terminal["complete_object_and_loaded_packets_checked"]
    assert terminal["lean_audit_sha256"] == digest(ROOT / "validation/lean.json")
    assert all(run["corrected_executions"] == run["typed_original_executions"] == 4128 for run in terminal["runs"])
    input_operand = json.loads((ROOT / "validation/input_operand.json").read_text(encoding="utf-8"))
    assert input_operand["passed"] and input_operand["actual_lean_codec_checked"] and input_operand["complete_loaded_and_object_packets_checked"]
    assert input_operand["lean_audit_sha256"] == digest(ROOT / "validation/lean.json")
    assert input_operand["dword_execution_checked"]
    assert input_operand["dword_proofs"] == lean["checked_dword_copy_declarations"]
    assert all(run["admissible_checks"] == 9 for run in input_operand["runs"])
    assert input_operand["runs"][1]["actual_natural_addresses_above_dword"]
    assert all(run["corrected_executions"] == run["typed_original_executions"] == 6400 for run in input_operand["runs"])
    dword_owner = json.loads((ROOT / "validation/dword_owner.json").read_text(encoding="utf-8"))
    assert dword_owner["passed"] and dword_owner["actual_lean_codec_checked"] and dword_owner["complete_loaded_and_object_packets_checked"]
    assert dword_owner["lean_audit_sha256"] == digest(ROOT / "validation/lean.json")
    assert all(run["executions"] == 6400 and run["complete_live_packets"] == 40 for run in dword_owner["runs"])
    with fitz.open(OUTPUT) as pdf:
        assert len(pdf) == 2, "The compact errata must remain two pages."
        text = normalized(" ".join(page.get_text() for page in pdf))
        for marker in [*[f"M{number:02d}." for number in range(1, 21)],
                       "Justification of the corrections", "10.24425/119359"]:
            assert marker in text, marker
        assert "Dolan" not in text
    tex = ERRATA / "morse-2018-errata.tex"
    log = ROOT / "output/pdf/morse-2018-errata.log"
    log_text = log.read_text(encoding="utf-8", errors="replace")
    assert "Overfull" not in log_text
    assert "Undefined control sequence" not in log_text
    assert "LaTeX Warning" not in log_text
    evidence = dict(as_of=date.today().isoformat(), source_sha256=digest(source),
                    source_excerpts_checked=len(edits), positive_proofs=PROOFS,
                    division_whole_byte_execution_checked=True, division_correctness_proofs=division_proofs,
                    pages=2, scope="M01-M20 exact local edits and positive correction contracts; full-paper and physical-ISA audit continues",
                    sources={str(path.relative_to(ROOT)).replace("\\", "/"): digest(path)
                             for path in [Path(__file__), ERRATA / "edits.json", tex, diff,
                                          ERRATA / "README.md", ERRATA / "POLICY.md", ROOT / "smcTuring/pure_smc.inc", ROOT / "smcTuring/listing6_smc.inc", ROOT / "smcTuring/listing5_smc.inc", ROOT / "smcTuring/terminal_smc.inc", ROOT / "smcTuring/dword_owner_smc.inc"]},
                    artifacts={"output/pdf/morse-2018-errata.pdf": digest(OUTPUT)},
                    lean_evidence_sha256=digest(ROOT / "validation/lean.json"),
                    division_evidence_sha256=digest(ROOT / "validation/division.json"),
                    terminal_evidence_sha256=digest(ROOT / "validation/terminal.json"), terminal_marker_checked=True, input_operand_checked=True,
                    input_operand_evidence_sha256=digest(ROOT / "validation/input_operand.json"),
                    dword_owner_checked=True, dword_owner_evidence_sha256=digest(ROOT / "validation/dword_owner.json"))
    (ROOT / "validation/errata.json").write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print(f"Errata: {len(edits)} exact published excerpts; {len(PROOFS)} audited positive proof references; two-page PDF")

if __name__ == "__main__":
    main()
