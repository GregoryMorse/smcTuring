"""Build the pinned Lean library and record the kernel theorem axiom audit."""
from __future__ import annotations

import argparse
import hashlib
from datetime import date
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from lean_build import lake_command
from memory_budget import require_budget

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean"


def main() -> None:
    require_budget()
    parser=argparse.ArgumentParser()
    parser.add_argument('--build-report',type=Path)
    args=parser.parse_args()
    sys.stdout.reconfigure(encoding="utf-8")
    toolchain = (PROJECT / "lean-toolchain").read_text().strip()
    folder = toolchain.replace("/", "--").replace(":", "---")
    binary = PROJECT / ".elan/toolchains" / folder / "bin"
    if not (binary / "lake.exe").is_file():
        raise SystemExit("Install the pinned toolchain locally first: " + toolchain)
    environment = dict(os.environ)
    environment["PATH"] = str(binary) + os.pathsep + environment["PATH"]
    report = {"as_of": date.today().isoformat(), "toolchain": toolchain,
              "version": subprocess.run([str(binary / "lean.exe"), "--version"],
                                        check=True, capture_output=True, text=True,
                                        encoding="utf-8").stdout.strip()}
    lake_command(PROJECT, binary)  # Configuration-equivalence check only.
    report["build_config"] = "lean/lakefile.proof.toml"
    commands=[("build", [sys.executable,str(ROOT/"validation/bounded_build.py"),
                                    "--report",str(ROOT/"validation/.build/full-bounded-build.json"),"SmcTuring"]),
                          ("audit", [sys.executable,str(ROOT/"validation/bounded_audit.py")])]
    if args.build_report:
        from bounded_snapshot import verify_build
        checked_build=verify_build(args.build_report)
        assert checked_build["targets"]==["SmcTuring"]
        report["build"]={"exit":0,"output":"Reused completed bounded build after validating all source, setup and artifact hashes.",
                         "report":str(args.build_report),"sha256":hashlib.sha256(args.build_report.read_bytes()).hexdigest()}
        commands=commands[1:]
    for name, command in commands:
        result = subprocess.run(command, cwd=PROJECT, env=environment,
                                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=1800 if name == "build" else 600)
        output = result.stdout + result.stderr
        report[name] = {"exit": result.returncode, "output": output}
        print(output, end="", flush=True)
        if result.returncode:
            raise SystemExit("Lean " + name + " failed")
    forbidden = ["sorryAx", "Lean.ofReduceBool"]
    assert not any(axiom in report["audit"]["output"] for axiom in forbidden)
    declarations = []
    audit_output = report["audit"]["output"]
    # Lean wraps long dependency lists across lines. Parse each complete bracket
    # so every declaration records the full actual kernel axiom inventory.
    pattern = r"^'([^'\r\n]+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(?:does not depend on any axioms))"
    for match in re.finditer(pattern, audit_output, re.MULTILINE):
        name, axioms = match.groups()
        found = re.findall('[A-Za-z_][A-Za-z0-9_.]*', axioms or '')
        assert set(found) <= {"propext", "Quot.sound", "Classical.choice"}, found
        declarations.append({"name": name, "axioms": found})
    assert len(declarations) == audit_output.count("depends on axioms:") + audit_output.count("does not depend on any axioms")
    assert len(declarations) >= 13, declarations
    expected=re.findall(r"^#print axioms (\S+)",(PROJECT/"Audit.lean").read_text(encoding="utf-8"),re.MULTILINE)
    assert [item["name"] for item in declarations]==expected, "Audit names differ from requested inventory"
    assert len(set(expected))==len(expected), "Duplicate requested audit"
    report["declarations"] = declarations
    report["bounded_build"] = checked_build if args.build_report else json.loads((ROOT/"validation/.build/full-bounded-build.json").read_text(encoding="utf-8"))
    assert report["bounded_build"]["passed"]
    report["verification_method"] = "Serial direct Lean with complete rc3 artifact levels, default kernel checking, -M768 -j1"
    paths = list(PROJECT.glob("*.lean")) + list((PROJECT / "SmcTuring").rglob("*.lean"))
    for path in paths:
        source = path.read_text(encoding="utf-8")
        assert not re.search(r'\b(sorry|admit|axiom)\b', source), path
    paths += [PROJECT / name for name in ["lean-toolchain", "lakefile.toml", "lakefile.proof.toml", "lake-manifest.json"]]
    paths += [ROOT / name for name in ["validation/lean_build.py", "validation/run_lean.py","validation/bounded_build.py",
       "validation/bounded_audit.py","validation/bounded_snapshot.py","validation/lean_export.py","validation/module_artifacts.py","validation/memory_budget.py","validation/limited_run.py"]]
    report["sources"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in paths}
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    report["dependency_revision"] = next(item["rev"] for item in manifest["packages"] if item["name"] == "mathlib")
    dependency_paths = [PROJECT / ".lake/packages/mathlib/Mathlib" / name for name in [
        "Computability/StateTransition.lean", "Computability/TuringMachine/Tape.lean",
        "Computability/TuringMachine/PostTuringMachine.lean", "Data/Fintype/Prod.lean",
        "Data/Fintype/Option.lean", "Data/Fintype/Card.lean", "Data/Fintype/EquivFin.lean", "Computability/Primrec/Basic.lean",
        "Computability/Primrec/List.lean", "Computability/Partrec.lean",
        "Computability/PartrecCode.lean", "Computability/PartrecBasis.lean",
        "Computability/TuringMachine/Config.lean", "Computability/TuringMachine/ToPartrec.lean",
        "Computability/TuringMachine/StackTuringMachine.lean", "Basic/Denumerable.lean", "Logic/Encodable/Basic.lean", "Logic/Equiv/Nat.lean",
        "Data/BitVec.lean"]]
    dependency_paths += [binary.parent / "src/lean/Init" / name for name in [
        "Data/Nat/Bitwise/Basic.lean", "Data/BitVec/Basic.lean", "Data/BitVec/Bootstrap.lean",
        "Data/BitVec/Lemmas.lean", "Data/Nat/Div/Basic.lean", "Data/List/OfFn.lean"]]
    report["dependency_sources"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                    for path in dependency_paths}
    converse_names = [
        "SmcTuring.SMC.Effective.concrete_finite_run_primrec",
        "SmcTuring.SMC.Effective.terminal_search_partrec",
        "SmcTuring.SMC.Effective.terminal_search_library_code",
        "SmcTuring.SMC.Effective.terminal_search_tm2",
        "SmcTuring.SMC.Effective.terminal_search_tm0_with_output",
        "SmcTuring.MathlibTM0.FiniteSupport.step_embedding",
        "SmcTuring.MathlibTM0.FiniteSupport.eval_eq",
        "SmcTuring.MathlibTM0.Numbering.transport_respects",
        "SmcTuring.MathlibTM0.Numbering.eval_eq",
        "SmcTuring.SMC.Effective.terminal_search_numbered_tm0",
        "SmcTuring.SMC.Effective.terminal_search_pure_smc"]
    assert set(converse_names) <= {item["name"] for item in declarations}
    report["converse_checked"] = True
    report["checked_converse_declarations"] = converse_names
    encoding_names = [
        "SmcTuring.Native.LittleEndian.word_decode_encode",
        "SmcTuring.Native.form_roundtrip",
        "SmcTuring.Native.ByteMemory.fetch_patched_moffs",
        "SmcTuring.Native.Layout.fields_and_owners_disjoint"]
    assert set(encoding_names) <= {item["name"] for item in declarations}
    report["selected_encoding_checked"] = True
    report["checked_encoding_declarations"] = encoding_names
    arithmetic_names = ["SmcTuring.Native.Arithmetic." + name for name in [
        "sbb_zero_mask", "xor_mask_select", "base_guard_accepts_heap",
        "base_guard_rejects_offset", "indexed_heap_address_toNat"]]
    assert set(arithmetic_names) <= {item["name"] for item in declarations}
    report["guard_arithmetic_checked"] = True
    report["checked_arithmetic_declarations"] = arithmetic_names
    execution_names = ["SmcTuring.Native.Execution." + name for name in [
        "execute_byte_encoding", "trace_preserves_carry", "sub_bridge_sbb_mask",
        "indirect_call_alias", "execute_patched_moffs"]]
    assert set(execution_names) <= {item["name"] for item in declarations}
    report["selected_execution_projection_checked"] = True
    report["checked_execution_declarations"] = execution_names
    fetch_names = ["SmcTuring.Native.Fetch." + name for name in [
        "encoded_length", "length_take_three", "fetch_current_encoding", "step_patched_moffs",
        "trace_head_step", "sub_bridge_sbb_mask"]]
    assert set(fetch_names) <= {item["name"] for item in declarations}
    report["automatic_fetch_checked"] = True
    report["checked_fetch_declarations"] = fetch_names
    reader_names = [
        "SmcTuring.Native.Writes.execute_memory",
        "SmcTuring.Native.Writes.put_word_back",
        "SmcTuring.Native.Reader.finish_memory",
        "SmcTuring.Native.Reader.fetch_last",
        "SmcTuring.Native.Reader.four_writes_owned",
        "SmcTuring.Native.Reader.trace_result"]
    assert set(reader_names) <= {item["name"] for item in declarations}
    report["byte_reader_checked"] = True
    report["checked_reader_declarations"] = reader_names
    call_names = ["SmcTuring.Native.Calls." + name for name in [
        "reset_memory", "stack_slot", "called_effect", "aliased_return", "called_top_word",
        "owned_run", "trace_result"]]
    assert set(call_names) <= {item["name"] for item in declarations}
    report["native_call_contracts_checked"] = True
    report["checked_native_call_declarations"] = call_names
    callee_names = ["SmcTuring.Native.ReadCallee." + name for name in [
        "target_pc", "memory_effect", "owned_run", "trace_result", "invocation_returns", "invocation_memory"]]
    assert set(callee_names) <= {item["name"] for item in declarations}
    report["native_read_callee_checked"] = True
    report["checked_native_read_callee_declarations"] = callee_names
    protected_names = [
        "SmcTuring.Native.Protected.current_moffs",
        "SmcTuring.Native.Protected.grid_store_protected",
        "SmcTuring.Native.Protected.trace_grid_protected",
        "SmcTuring.Native.GridImage.initially_protected",
        "SmcTuring.Native.GridImage.initial_word",
        "SmcTuring.Native.GridImage.initial_fetch"]
    assert set(protected_names) <= {item["name"] for item in declarations}
    report["native_storage_grid_checked"] = True
    report["checked_native_storage_grid_declarations"] = protected_names
    image_names = [
        "SmcTuring.Native.ControlImage.fetch_current",
        "SmcTuring.Native.ControlImage.store_intact",
        "SmcTuring.Native.ControlPacking.placed_separated",
        "SmcTuring.Native.ControlPacking.initial_fetch",
        "SmcTuring.Native.ControlPacking.step_at_entry",
        "SmcTuring.Native.CombinedImage.initially_intact",
        "SmcTuring.Native.CombinedImage.initial_word",
        "SmcTuring.Native.CombinedImage.owned_operand",
        "SmcTuring.Native.CombinedImage.trace_intact"]
    assert set(image_names) <= {item["name"] for item in declarations}
    report["native_combined_image_checked"] = True
    report["checked_native_combined_image_declarations"] = image_names
    reader_image_names = ["SmcTuring.Native.ReaderImage." + name for name in [
        "placed_roles", "label_owned", "first_hits", "second_hits", "trace", "owned_run",
        "finish_position", "initial_pointer", "initialized_trace", "initialized_accumulator"]]
    assert set(reader_image_names) <= {item["name"] for item in declarations}
    report["native_reader_image_checked"] = True
    report["checked_native_reader_image_declarations"] = reader_image_names
    relocation_names = ["SmcTuring.Native.Relocation." + name for name in [
        "relative32_toInt", "sign_extended_relative32", "memory_hits",
        "instruction_memory_hits", "relative_call_pc", "relative_call_position"]]
    assert set(relocation_names) <= {item["name"] for item in declarations}
    report["native_relocation_checked"] = True
    report["checked_native_relocation_declarations"] = relocation_names
    fragment_names = [
        "SmcTuring.Native.Fragment.place_append",
        "SmcTuring.Native.Fragment.initialized_owned_word",
        "SmcTuring.Native.Fragment.owned_packet_safe",
        "SmcTuring.Native.Fragment.owned_fields_separate",
        "SmcTuring.Native.ReaderView.trace",
        "SmcTuring.Native.ReaderView.owned_run"]
    assert set(fragment_names) <= {item["name"] for item in declarations}
    report["native_fragment_view_checked"] = True
    report["checked_native_fragment_view_declarations"] = fragment_names
    placed_call_names = ["SmcTuring.Native.CallsImage." + name for name in [
        "placed_roles", "reset_ready", "indirect_hits", "trace", "owned_run", "target_pc"]]
    assert set(placed_call_names) <= {item["name"] for item in declarations}
    report["native_placed_calls_checked"] = True
    report["checked_native_placed_calls_declarations"] = placed_call_names
    placed_callee_names = ["SmcTuring.Native.ReadCalleeImage." + name for name in [
        "ready", "return_next", "trace", "owned_run", "finish_intact", "memory_effect",
        "boundary_effect", "top_reusable", "initialized_ready", "initialized_trace", "initialized_owned_run"]]
    assert set(placed_callee_names) <= {item["name"] for item in declarations}
    report["native_placed_read_callee_checked"] = True
    report["checked_native_placed_read_callee_declarations"] = placed_callee_names
    read_invocation_names = ["SmcTuring.Native.ReadInvocationImage." + name for name in [
        "caller_label", "callee_ready", "trace", "owned_run", "return_position", "memory_effect",
        "accumulator", "carry", "top_reusable", "finish_intact", "memory_frame", "program_count"]]
    assert set(read_invocation_names) <= {item["name"] for item in declarations}
    report["native_read_invocation_checked"] = True
    report["checked_native_read_invocation_declarations"] = read_invocation_names
    store_callee_names = ["SmcTuring.Native.StoreCalleeImage." + name for name in [
        "store_pc", "store_fetch", "trace", "owned_run", "return_pc", "memory_effect",
        "accumulator", "carry", "top_reusable", "finish_intact", "program_count"]]
    assert set(store_callee_names) <= {item["name"] for item in declarations}
    report["native_store_callee_checked"] = True
    report["checked_native_store_callee_declarations"] = store_callee_names
    store_invocation_names = ["SmcTuring.Native.StoreInvocationImage." + name for name in [
        "callee_ready", "trace", "owned_run", "return_position", "memory_effect", "accumulator",
        "carry", "top_reusable", "finish_intact", "memory_frame", "program_count"]]
    store_invocation_names += ["SmcTuring.Native.Writes.put_bytes_commute", "SmcTuring.Native.Writes.put_words_commute"]
    assert set(store_invocation_names) <= {item["name"] for item in declarations}
    report["native_store_invocation_checked"] = True
    report["checked_native_store_invocation_declarations"] = store_invocation_names
    spaced_names = ["SmcTuring.Native.SpacedPacking." + name for name in [
        "adjacent_size", "adjacent_place", "place_append", "placed_separated", "initial_packet",
        "initial_fetch", "uncovered_frame", "adjacent_member"]]
    spaced_names += ["SmcTuring.Native.SpacedCombinedImage." + name for name in [
        "initially_intact", "initial_word", "store_intact", "owned_operand", "trace_intact",
        "adjacent_image", "adjacent_intact", "adjacent_owned", "padding_byte"]]
    assert set(spaced_names) <= {item["name"] for item in declarations}
    report["native_spaced_image_checked"] = True
    report["checked_native_spaced_image_declarations"] = spaced_names
    aligned_names = ["SmcTuring.Native.AlignedPacking." + name for name in [
        "alignment_small", "aligned_end", "reader_extra_constant", "reader_field_aligned",
        "scalar_extra_constant", "scalar_field_aligned", "reader_label_aligned", "scalar_label_location", "scalar_label_aligned"]]
    assert set(aligned_names) <= {item["name"] for item in declarations}
    report["native_aligned_packing_checked"] = True
    report["checked_native_aligned_packing_declarations"] = aligned_names
    scalar_names = ["SmcTuring.Native.ScalarImage." + name for name in [
        "store_size", "transport_ready", "sbb_size", "hits", "fetch", "trace", "owned_run", "position", "memory_effect", "written_value",
        "accumulator", "stack", "carry", "store_carry", "load_frame", "finish_intact", "zero_mask", "zero_carry"]]
    assert set(scalar_names) <= {item["name"] for item in declarations}
    report["native_scalar_image_checked"] = True
    report["checked_native_scalar_image_declarations"] = scalar_names
    borrow_mask_names = ["SmcTuring.Native.BorrowMaskImage." + name for name in [
        "transport_ready",
        "read_ready", "read_zero", "store_ready", "sbb_ready", "borrow_reaches_sbb", "mask", "trace", "owned_run",
        "position", "carry", "finish_intact", "top_reusable", "memory_effect", "memory_frame", "load_frame",
        "zero_reusable", "pointer_reusable", "program_count"]]
    assert set(borrow_mask_names) <= {item["name"] for item in declarations}
    report["native_borrow_mask_checked"] = True
    report["checked_native_borrow_mask_declarations"] = borrow_mask_names
    guard_setup_names = [
        'SmcTuring.Native.ReadInvocationImage.transport_ready',
        'SmcTuring.Native.ReadInvocationImage.load_frame',
        'SmcTuring.Native.ScalarImage.transport_ready',
        'SmcTuring.Native.ScalarImage.store_size',
    ] + ["SmcTuring.Native.GuardSetupImage." + name for name in [
        "transport_ready",
        'capture_memory', 'capture_accumulator', 'capture_trace', 'capture_owned_run', 'resume_ready',
        'resumed_load_frame', 'candidate_ready', 'candidate_owned', 'candidate_accumulator', 'scratch_ready',
        'scratched_load_frame', 'boundary_ready', 'boundary_owned', 'accumulator', 'saved_resume',
        'saved_candidate', 'stack', 'carry', 'pc', 'position',
        'finish_intact', 'top_reusable', 'load_frame', 'trace', 'owned_run',
        'memory_effect', 'memory_frame', 'boundary_value_reusable', 'boundary_pointer_reusable', 'run',
        'program_count',
    ]]
    assert set(guard_setup_names) <= {item["name"] for item in declarations}
    report["native_guard_setup_checked"] = True
    report["checked_native_guard_setup_declarations"] = guard_setup_names
    native_read_scalar_names = ["SmcTuring.Native.ReadScalarImage." + name for name in [
        'transport_ready', 'scalar_ready', 'read_value_from', 'read_accumulator', 'target_before_scalar',
        'trace', 'owned_run', 'written_value', 'memory_effect', 'accumulator',
        'stack', 'carry', 'xor_carry', 'and_carry', 'pc',
        'position', 'finish_intact', 'top_reusable', 'load_frame', 'memory_frame',
        'run', 'program_count',
    ]]
    assert set(native_read_scalar_names) <= {item["name"] for item in declarations}
    report["native_read_scalar_checked"] = True
    report["checked_native_read_scalar_declarations"] = native_read_scalar_names
    native_guard_selection_names = ["SmcTuring.Native.GuardSelectionImage." + name for name in [
        'transport_ready', 'first_load_frame', 'second_ready', 'second_load_frame', 'third_ready',
        'third_load_frame', 'fourth_ready', 'fourth_load_frame', 'continuation_owned', 'terminal_owned',
        'mask_owned', 'first_read_value', 'second_read_value', 'third_read_value', 'fourth_read_value',
        'first_selected', 'second_selected', 'third_selected', 'fourth_selected', 'selected_slot_separate',
        'collapse_memory', 'first_memory', 'second_memory', 'third_memory', 'fourth_memory',
        'call_location', 'call_top', 'call_intact', 'call_stack_ready', 'call_trace',
        'call_owned_run', 'before_trace', 'before_owned_run', 'trace', 'owned_run',
        'pc', 'selects', 'stack', 'carry', 'accumulator',
        'call_memory', 'memory_effect', 'memory_frame', 'finish_intact', 'load_frame',
        'top_reusable', 'selected_word', 'slot_word', 'run', 'program_count',
    ]]
    assert set(native_guard_selection_names) <= {item["name"] for item in declarations}
    report["native_guard_selection_checked"] = True
    report["checked_native_guard_selection_declarations"] = native_guard_selection_names
    native_guard_image_names = ["SmcTuring.Native.GuardImage." + name for name in [
        'transport_ready', 'different_roles', 'setup_frame_role', 'borrow_ready', 'borrow_frame_role',
        'selection_ready', 'borrow_carry', 'mask_value', 'saved_resume', 'terminal_owned',
        'terminal_value', 'pc', 'trace', 'owned_run', 'stack',
        'carry', 'accumulator', 'finish_intact', 'top_reusable', 'load_frame',
        'selected_word', 'slot_word', 'memory_effect', 'memory_frame', 'run',
        'program_count',
    ]]
    assert set(native_guard_image_names) <= {item["name"] for item in declarations}
    report["native_guard_image_checked"] = True
    report["checked_native_guard_image_declarations"] = native_guard_image_names
    native_guard_invocation_names = ["SmcTuring.Native.GuardInvocationImage." + name for name in [
        'metadata_owned', 'metadata_not_slot', 'transport_ready',
        'caller_run', 'caller_ready', 'caller_pc', 'caller_memory', 'caller_memory_nat',
        'caller_return_word', 'caller_trace', 'caller_owned_run', 'caller_intact', 'caller_load_frame',
        'caller_role_frame', 'capture_label_owned', 'body_ready', 'candidate_value', 'boundary_value',
        'borrowed_after_caller', 'terminal_value', 'pc', 'trace', 'owned_run',
        'stack', 'carry', 'accumulator', 'finish_intact', 'top_reusable',
        'load_frame', 'selected_word', 'slot_word', 'memory_effect', 'memory_frame',
        'run', 'program_count',
    ]]
    assert set(native_guard_invocation_names) <= {item["name"] for item in declarations}
    report["native_guard_invocation_checked"] = True
    report["checked_native_guard_invocation_declarations"] = native_guard_invocation_names
    native_source_values_names = ["SmcTuring.Native.SourceValues." + name for name in [
        'natural_injective', 'word_toNat', 'word_injective', 'word_borrow', 'offset_sum_below_boundary',
        'offset_sum_borrow', 'address_candidate_borrow', 'typed_guard_borrow', 'typed_guard_pc', 'address_guard_borrow',
        'address_guard_pc', 'source_address_encoded', 'source_address_toNat',
    ]]
    assert set(native_source_values_names) <= {item["name"] for item in declarations}
    report["native_source_values_checked"] = True
    report["checked_native_source_values_declarations"] = native_source_values_names
    native_source_data_names = ["SmcTuring.Native.SourceData." + name for name in [
        'base_fits', 'metadata_fits',
        'field_fits', 'register_fits', 'heap_index_inside', 'heap_fits', 'register_toNat',
        'heap_toNat', 'register_owned', 'heap_owned', 'register_injective', 'heap_address_injective',
        'heap_injective', 'register_heap_separate', 'field_not_before', 'register_not_before', 'heap_not_before',
        'boundary_fits', 'value_fits', 'address_fits', 'initial_register_value', 'initial_heap_value',
        'initial_rep',
    ]]
    assert set(native_source_data_names) <= {item["name"] for item in declarations}
    report["native_source_data_checked"] = True
    report["checked_native_source_data_declarations"] = native_source_data_names
    native_immediate_image_names = ["SmcTuring.Native.ImmediateImage." + name for name in [
        'read_value', 'destination_value', 'other_register_frame', 'heap_frame', 'represented',
        'source_step', 'memory_effect', 'correct',
    ]]
    assert set(native_immediate_image_names) <= {item["name"] for item in declarations}
    report["native_immediate_image_checked"] = True
    report["checked_native_immediate_image_declarations"] = native_immediate_image_names
    native_offset_guard_names = ["SmcTuring.Native.OffsetGuardImage." + name for name in [
        'load_frame',
        'field_fits', 'data_not_field', 'metadata_after_read', 'guard_ready', 'read_value',
        'candidate_after_read', 'boundary_after_read', 'terminal_after_read', 'after_read_data_frame', 'data_frame',
        'represented', 'trace', 'owned_run', 'pc', 'stack',
        'carry', 'accumulator', 'finish_intact', 'top_reusable', 'selected_word',
        'slot_word', 'memory_frame', 'run', 'program_count', 'correct',
    ]]
    assert set(native_offset_guard_names) <= {item["name"] for item in declarations}
    report["native_offset_guard_checked"] = True
    report["checked_native_offset_guard_declarations"] = native_offset_guard_names
    native_pointer_image_names = ["SmcTuring.Native.PointerImage." + name for name in [
        'metadata_owned', 'transport_ready', 'base_load_frame', 'offset_ready', 'offset_load_frame',
        'word_ready', 'field_fits', 'data_not_field', 'base_value', 'offset_value',
        'pointer_after_base', 'pointer_after_offset', 'word_value', 'candidate', 'pointer',
        'load_frame', 'represented', 'trace', 'owned_run', 'pc',
        'finish_intact', 'source_address', 'run', 'program_count', 'correct',
    ]]
    assert set(native_pointer_image_names) <= {item["name"] for item in declarations}
    report["native_pointer_image_checked"] = True
    report["checked_native_pointer_image_declarations"] = native_pointer_image_names
    native_address_image_names = ["SmcTuring.Native.AddressImage." + name for name in [
        'pointer_metadata_frame', 'pointer_ready', 'guard_metadata_frame', 'guard_ready', 'candidate',
        'boundary', 'terminal', 'accepted_pc', 'pc', 'accepted_trace',
        'trace', 'accepted_owned_run', 'owned_run', 'accepted_data_frame', 'accepted_represented',
        'represented', 'pointer', 'finish_intact', 'carry', 'load_frame',
        'top_reusable', 'stack', 'run', 'program_count', 'correct',
    ]]
    assert set(native_address_image_names) <= {item["name"] for item in declarations}
    report["native_address_image_checked"] = True
    report["checked_native_address_image_declarations"] = native_address_image_names
    native_computed_pointer_names = [
        'SmcTuring.Native.ReadInvocationImage.transport_ready_pointer',
        'SmcTuring.Native.ReadScalarImage.transport_ready_pointer',
        'SmcTuring.Native.StoreInvocationImage.transport_ready_pointer',
        'SmcTuring.Native.StoreInvocationImage.written_value',
        'SmcTuring.Native.StoreInvocationImage.load_frame',
    ]
    assert set(native_computed_pointer_names) <= {item["name"] for item in declarations}
    report["native_computed_pointer_checked"] = True
    report["checked_native_computed_pointer_declarations"] = native_computed_pointer_names
    native_source_write_names = [
        'SmcTuring.Native.SourceWriteImage.register_rep',
        'SmcTuring.Native.SourceWriteImage.heap_rep',
    ]
    assert set(native_source_write_names) <= {item["name"] for item in declarations}
    report["native_source_write_checked"] = True
    report["checked_native_source_write_declarations"] = native_source_write_names
    native_load_image_names = [
        'SmcTuring.Native.LoadImage.pointer_inside',
        'SmcTuring.Native.LoadImage.read_ready',
        'SmcTuring.Native.LoadImage.read_value',
        'SmcTuring.Native.LoadImage.source_step',
        'SmcTuring.Native.LoadImage.represented',
        'SmcTuring.Native.LoadImage.trace',
        'SmcTuring.Native.LoadImage.owned_run',
        'SmcTuring.Native.LoadImage.pc',
        'SmcTuring.Native.LoadImage.finish_intact',
        'SmcTuring.Native.LoadImage.top_reusable',
        'SmcTuring.Native.LoadImage.stack',
        'SmcTuring.Native.LoadImage.carry',
        'SmcTuring.Native.LoadImage.load_frame',
        'SmcTuring.Native.LoadImage.run',
        'SmcTuring.Native.LoadImage.program_count',
        'SmcTuring.Native.LoadImage.correct',
    ]
    assert set(native_load_image_names) <= {item["name"] for item in declarations}
    report["native_load_image_checked"] = True
    report["checked_native_load_image_declarations"] = native_load_image_names
    native_program_composition_names = ['SmcTuring.Native.BlockImage.address_ready_from_snapshot', 'SmcTuring.Native.BlockImage.ready_from_snapshot', 'SmcTuring.Native.BlockImage.correct', 'SmcTuring.Native.BlockImage.load_frame', 'SmcTuring.Native.BlockImage.load_pointer', 'SmcTuring.Native.BlockImage.store_pointer', 'SmcTuring.Native.ProgramImage.block_ready', 'SmcTuring.Native.ProgramImage.block_frames', 'SmcTuring.Native.ProgramImage.block_selected', 'SmcTuring.Native.ProgramImage.block_invariant', 'SmcTuring.Native.ProgramImage.correct', 'SmcTuring.Native.ProgramImage.successful_boundary']
    assert set(native_program_composition_names) <= {item["name"] for item in declarations}
    report["native_program_composition_checked"] = True
    report["checked_native_program_composition_declarations"] = native_program_composition_names
    native_loop_image_names = ['SmcTuring.Native.LoopImage.correct', 'SmcTuring.Native.LoopImage.pass_correct']
    assert set(native_loop_image_names) <= {item["name"] for item in declarations}
    report["native_loop_image_checked"] = True
    report["checked_native_loop_image_declarations"] = native_loop_image_names
    native_kernel_schedule_names = ['SmcTuring.Native.KernelImage.lower_properties', 'SmcTuring.Native.KernelImage.compile_properties', 'SmcTuring.Native.KernelImage.compile_total', 'SmcTuring.Native.KernelImage.kernel_supported', 'SmcTuring.Native.KernelImage.fixed_kernel']
    assert set(native_kernel_schedule_names) <= {item["name"] for item in declarations}
    report["native_kernel_schedule_checked"] = True
    report["checked_native_kernel_schedule_declarations"] = native_kernel_schedule_names
    native_kernel_packets_names = ['SmcTuring.Native.KernelPackets.ordered_size', 'SmcTuring.Native.KernelPackets.ordered_placement', 'SmcTuring.Native.KernelPackets.scalar_size', 'SmcTuring.Native.KernelPackets.read_scalar_size', 'SmcTuring.Native.KernelPackets.read_scalar_placement', 'SmcTuring.Native.KernelPackets.source_ordered', 'SmcTuring.Native.KernelPackets.source_continuation', 'SmcTuring.Native.KernelPackets.ordered_append', 'SmcTuring.Native.KernelPackets.program_ordered', 'SmcTuring.Native.KernelPackets.global_placement', 'SmcTuring.Native.KernelPackets.global_read_scalar', 'SmcTuring.Native.KernelPackets.source_packet_count', 'SmcTuring.Native.KernelPackets.program_packet_count', 'SmcTuring.Native.KernelPackets.kernel_packet_count']
    assert set(native_kernel_packets_names) <= {item["name"] for item in declarations}
    report["native_kernel_packets_checked"] = True
    report["checked_native_kernel_packets_declarations"] = native_kernel_packets_names
    native_guard_packets_names = ['SmcTuring.Native.GuardPackets.ordered', 'SmcTuring.Native.GuardPackets.packet_count', 'SmcTuring.Native.GuardPackets.global_placement']
    assert set(native_guard_packets_names) <= {item["name"] for item in declarations}
    report["native_guard_packets_checked"] = True
    report["checked_native_guard_packets_declarations"] = native_guard_packets_names
    native_store_image_names = [
        'SmcTuring.Native.StoreImage.pointer_inside',
        'SmcTuring.Native.StoreImage.source_label_frame',
        'SmcTuring.Native.StoreImage.read_ready',
        'SmcTuring.Native.StoreImage.read_value',
        'SmcTuring.Native.StoreImage.pointer_after_read',
        'SmcTuring.Native.StoreImage.store_ready',
        'SmcTuring.Native.StoreImage.after_read_represented',
        'SmcTuring.Native.StoreImage.source_step',
        'SmcTuring.Native.StoreImage.represented',
        'SmcTuring.Native.StoreImage.accepted_trace',
        'SmcTuring.Native.StoreImage.trace',
        'SmcTuring.Native.StoreImage.accepted_owned_run',
        'SmcTuring.Native.StoreImage.owned_run',
        'SmcTuring.Native.StoreImage.pc',
        'SmcTuring.Native.StoreImage.finish_intact',
        'SmcTuring.Native.StoreImage.top_reusable',
        'SmcTuring.Native.StoreImage.stack',
        'SmcTuring.Native.StoreImage.carry',
        'SmcTuring.Native.StoreImage.load_frame',
        'SmcTuring.Native.StoreImage.run',
        'SmcTuring.Native.StoreImage.program_count',
        'SmcTuring.Native.StoreImage.correct',
    ]
    assert set(native_store_image_names) <= {item["name"] for item in declarations}
    report["native_store_image_checked"] = True
    report["checked_native_store_image_declarations"] = native_store_image_names
    native_aligned_templates_names = ['SmcTuring.Native.AlignedTemplates.padded_size', 'SmcTuring.Native.AlignedTemplates.padded_place', 'SmcTuring.Native.AlignedTemplates.padded_within', 'SmcTuring.Native.AlignedTemplates.reader_extent', 'SmcTuring.Native.AlignedTemplates.scalar_extent', 'SmcTuring.Native.AlignedTemplates.reader_constructed', 'SmcTuring.Native.AlignedTemplates.scalar_constructed']
    assert set(native_aligned_templates_names) <= {item["name"] for item in declarations}
    report["native_aligned_templates_checked"] = True
    report["checked_native_aligned_templates_declarations"] = native_aligned_templates_names
    native_aligned_pool_names = ['SmcTuring.Native.AlignedPool.pool_extent', 'SmcTuring.Native.AlignedPool.end_cursor', 'SmcTuring.Native.AlignedPool.reader_cursor', 'SmcTuring.Native.AlignedPool.pool_constructed']
    assert set(native_aligned_pool_names) <= {item["name"] for item in declarations}
    report["native_aligned_pool_checked"] = True
    report["checked_native_aligned_pool_declarations"] = native_aligned_pool_names
    native_role_initialization_names = ['SmcTuring.Native.RoleInitialization.reader_count', 'SmcTuring.Native.RoleInitialization.field_count', 'SmcTuring.Native.RoleInitialization.reader_at_index', 'SmcTuring.Native.RoleInitialization.field_at_index', 'SmcTuring.Native.RoleInitialization.reader_initialized', 'SmcTuring.Native.RoleInitialization.field_initialized']
    assert set(native_role_initialization_names) <= {item["name"] for item in declarations}
    report["native_role_initialization_checked"] = True
    report["checked_native_role_initialization_declarations"] = native_role_initialization_names
    native_byte_lengths_names = ['SmcTuring.Native.ByteLengths.source_end', 'SmcTuring.Native.ByteLengths.source_size', 'SmcTuring.Native.ByteLengths.guard_end', 'SmcTuring.Native.ByteLengths.guard_size', 'SmcTuring.Native.ByteLengths.program_size', 'SmcTuring.Native.ByteLengths.compile_extent', 'SmcTuring.Native.ByteLengths.kernel_span']
    assert set(native_byte_lengths_names) <= {item["name"] for item in declarations}
    report["native_byte_lengths_checked"] = True
    report["checked_native_byte_lengths_declarations"] = native_byte_lengths_names
    native_metadata_geometry_names = ['SmcTuring.Native.MetadataGeometry.scalar_step', 'SmcTuring.Native.MetadataGeometry.scalar_step_aligned', 'SmcTuring.Native.MetadataGeometry.scalar_field_affine', 'SmcTuring.Native.MetadataGeometry.field_affine', 'SmcTuring.Native.MetadataGeometry.field_index_injective', 'SmcTuring.Native.MetadataGeometry.field_position_injective', 'SmcTuring.Native.MetadataGeometry.field_word_injective']
    assert set(native_metadata_geometry_names) <= {item["name"] for item in declarations}
    report["native_metadata_geometry_checked"] = True
    report["checked_native_metadata_geometry_declarations"] = native_metadata_geometry_names
    native_layout_pass_names = ['SmcTuring.Native.LayoutPass.reader_extent', 'SmcTuring.Native.LayoutPass.field_extent', 'SmcTuring.Native.LayoutPass.guard_extent', 'SmcTuring.Native.LayoutPass.prefix_extent', 'SmcTuring.Native.LayoutPass.compiled_extent', 'SmcTuring.Native.LayoutPass.body_extent', 'SmcTuring.Native.LayoutPass.backedge_extent', 'SmcTuring.Native.LayoutPass.grid_aligned']
    assert set(native_layout_pass_names) <= {item["name"] for item in declarations}
    report["native_layout_pass_checked"] = True
    report["checked_native_layout_pass_declarations"] = native_layout_pass_names
    native_emitted_image_names = ['SmcTuring.Native.EmittedImage.reserve_size', 'SmcTuring.Native.EmittedImage.reserve_place', 'SmcTuring.Native.EmittedImage.body_extent', 'SmcTuring.Native.EmittedImage.whole_extent', 'SmcTuring.Native.EmittedImage.grid_gap', 'SmcTuring.Native.EmittedImage.grid_enough', 'SmcTuring.Native.EmittedImage.initially_intact', 'SmcTuring.Native.EmittedImage.initially_represented']
    assert set(native_emitted_image_names) <= {item["name"] for item in declarations}
    report["native_emitted_image_checked"] = True
    report["checked_native_emitted_image_declarations"] = native_emitted_image_names
    native_image_initialization_names = ['SmcTuring.Native.ImageInitialization.metadata_within', 'SmcTuring.Native.ImageInitialization.reader_initialized', 'SmcTuring.Native.ImageInitialization.field_initialized']
    assert set(native_image_initialization_names) <= {item["name"] for item in declarations}
    report["native_image_initialization_checked"] = True
    report["checked_native_image_initialization_declarations"] = native_image_initialization_names
    native_recontext_names = ['SmcTuring.Native.Recontext.block_instruction', 'SmcTuring.Native.Recontext.block_start', 'SmcTuring.Native.Recontext.block_continuation', 'SmcTuring.Native.Recontext.block_context', 'SmcTuring.Native.Recontext.block_segments', 'SmcTuring.Native.Recontext.program_segments', 'SmcTuring.Native.Recontext.lower', 'SmcTuring.Native.Recontext.compile', 'SmcTuring.Native.Recontext.layout_roles', 'SmcTuring.Native.Recontext.guard_packets', 'SmcTuring.Native.Recontext.layout_prefix', 'SmcTuring.Native.Recontext.emitted_image', 'SmcTuring.Native.Recontext.constructed_kernel']
    assert set(native_recontext_names) <= {item["name"] for item in declarations}
    report["native_recontext_checked"] = True
    report["checked_native_recontext_declarations"] = native_recontext_names
    native_pool_geometry_names = ['SmcTuring.Native.PoolGeometry.cursor_succ', 'SmcTuring.Native.PoolGeometry.reader_next_start', 'SmcTuring.Native.PoolGeometry.reader_start_affine', 'SmcTuring.Native.PoolGeometry.reader_bound', 'SmcTuring.Native.PoolGeometry.scalar_end', 'SmcTuring.Native.PoolGeometry.scalar_bound']
    assert set(native_pool_geometry_names) <= {item["name"] for item in declarations}
    report["native_pool_geometry_checked"] = True
    report["checked_native_pool_geometry_declarations"] = native_pool_geometry_names
    native_bounded_initialization_names = ['SmcTuring.Native.BoundedInitialization.metadata_before_grid', 'SmcTuring.Native.BoundedInitialization.metadata_fits', 'SmcTuring.Native.BoundedInitialization.reader_limit_le', 'SmcTuring.Native.BoundedInitialization.reader_fits', 'SmcTuring.Native.BoundedInitialization.field_fits', 'SmcTuring.Native.BoundedInitialization.field_bound', 'SmcTuring.Native.BoundedInitialization.field_before_grid', 'SmcTuring.Native.BoundedInitialization.readers_initialized', 'SmcTuring.Native.BoundedInitialization.fields_initialized', 'SmcTuring.Native.BoundedInitialization.field_owned', 'SmcTuring.Native.BoundedInitialization.reader_owned', 'SmcTuring.Native.BoundedInitialization.reader_target_owned', 'SmcTuring.Native.BoundedInitialization.stack_top_value']
    assert set(native_bounded_initialization_names) <= {item["name"] for item in declarations}
    report["native_bounded_initialization_checked"] = True
    report["checked_native_bounded_initialization_declarations"] = native_bounded_initialization_names
    native_assembly_names = ['SmcTuring.Native.Assembly.exists_image', 'SmcTuring.Native.Assembly.common_context', 'SmcTuring.Native.Assembly.boundary_bound', 'SmcTuring.Native.Assembly.backedge_fits', 'SmcTuring.Native.Assembly.compiled_bounds', 'SmcTuring.Native.Assembly.source_segment_within', 'SmcTuring.Native.Assembly.source_read_scalar_within', 'SmcTuring.Native.Assembly.initially_intact', 'SmcTuring.Native.Assembly.initially_represented']
    assert set(native_assembly_names) <= {item["name"] for item in declarations}
    report["native_assembly_checked"] = True
    report["checked_native_assembly_declarations"] = native_assembly_names
    native_guard_placement_names = ['SmcTuring.Native.GuardPlacement.guard_within', 'SmcTuring.Native.GuardPlacement.segment_within', 'SmcTuring.Native.GuardPlacement.read_scalar_within', 'SmcTuring.Native.GuardPlacement.capture_within', 'SmcTuring.Native.GuardPlacement.capture_constructed']
    assert set(native_guard_placement_names) <= {item["name"] for item in declarations}
    report["native_guard_placement_checked"] = True
    report["checked_native_guard_placement_declarations"] = native_guard_placement_names
    native_role_separation_names = ['SmcTuring.Native.RoleSeparation.position_injective', 'SmcTuring.Native.RoleSeparation.position_bounds', 'SmcTuring.Native.RoleSeparation.operand_owned', 'SmcTuring.Native.RoleSeparation.position_fits', 'SmcTuring.Native.RoleSeparation.word_injective', 'SmcTuring.Native.RoleSeparation.field_different', 'SmcTuring.Native.RoleSeparation.reader_field_different', 'SmcTuring.Native.RoleSeparation.capture_field_different', 'SmcTuring.Native.RoleSeparation.reader_different', 'SmcTuring.Native.RoleSeparation.guard_role_word', 'SmcTuring.Native.RoleSeparation.guard_roles_injective']
    assert set(native_role_separation_names) <= {item["name"] for item in declarations}
    report["native_role_separation_checked"] = True
    report["checked_native_role_separation_declarations"] = native_role_separation_names
    native_readiness_atoms_names = ['SmcTuring.Native.ReadinessAtoms.compact_delta', 'SmcTuring.Native.ReadinessAtoms.destination_bounds', 'SmcTuring.Native.ReadinessAtoms.destination_owned', 'SmcTuring.Native.ReadinessAtoms.destination_not_field', 'SmcTuring.Native.ReadinessAtoms.calls_bounds', 'SmcTuring.Native.ReadinessAtoms.calls_ranges', 'SmcTuring.Native.ReadinessAtoms.reader_ready', 'SmcTuring.Native.ReadinessAtoms.destination_fits', 'SmcTuring.Native.ReadinessAtoms.scalar_ready', 'SmcTuring.Native.ReadinessAtoms.read_scalar_ready']
    assert set(native_readiness_atoms_names) <= {item["name"] for item in declarations}
    report["native_readiness_atoms_checked"] = True
    report["checked_native_readiness_atoms_declarations"] = native_readiness_atoms_names
    native_guard_readiness_names = ['SmcTuring.Native.GuardReadiness.setup_ready', 'SmcTuring.Native.GuardReadiness.borrow_ready', 'SmcTuring.Native.GuardReadiness.selection_ready', 'SmcTuring.Native.GuardReadiness.guard_ready']
    assert set(native_guard_readiness_names) <= {item["name"] for item in declarations}
    report["native_guard_readiness_checked"] = True
    report["checked_native_guard_readiness_declarations"] = native_guard_readiness_names
    native_loop_initialization_names = ['SmcTuring.Native.LoopInitialization.frozen_owned', 'SmcTuring.Native.LoopInitialization.frozen_not_slot', 'SmcTuring.Native.LoopInitialization.backedge_within', 'SmcTuring.Native.LoopInitialization.initial_invariant', 'SmcTuring.Native.LoopInitialization.loop_setup']
    assert set(native_loop_initialization_names) <= {item["name"] for item in declarations}
    report["native_loop_initialization_checked"] = True
    report["checked_native_loop_initialization_declarations"] = native_loop_initialization_names
    native_compiled_layout_names = ['SmcTuring.Native.CompiledLayout.compile_membership', 'SmcTuring.Native.CompiledLayout.block_lowered', 'SmcTuring.Native.CompiledLayout.offset_field_position', 'SmcTuring.Native.CompiledLayout.pointer_field_position', 'SmcTuring.Native.CompiledLayout.address_field_position', 'SmcTuring.Native.CompiledLayout.guard_metadata_word', 'SmcTuring.Native.CompiledLayout.pointer_metadata_word', 'SmcTuring.Native.CompiledLayout.guard_metadata_frozen', 'SmcTuring.Native.CompiledLayout.pointer_metadata_frozen', 'SmcTuring.Native.CompiledLayout.address_static_frozen', 'SmcTuring.Native.CompiledLayout.static_frozen', 'SmcTuring.Native.CompiledLayout.frozen_not_address_field', 'SmcTuring.Native.CompiledLayout.frozen_before_grid', 'SmcTuring.Native.CompiledLayout.frozen_outside']
    assert set(native_compiled_layout_names) <= {item["name"] for item in declarations}
    report["native_compiled_layout_checked"] = True
    report["checked_native_compiled_layout_declarations"] = native_compiled_layout_names
    native_invocation_readiness_names = ['SmcTuring.Native.InvocationReadiness.reader_for', 'SmcTuring.Native.InvocationReadiness.update_for', 'SmcTuring.Native.InvocationReadiness.guard_for', 'SmcTuring.Native.InvocationReadiness.store_for']
    assert set(native_invocation_readiness_names) <= {item["name"] for item in declarations}
    report["native_invocation_readiness_checked"] = True
    report["checked_native_invocation_readiness_declarations"] = native_invocation_readiness_names
    native_source_separation_names = ['SmcTuring.Native.SourceSeparation.guard_offset_separate', 'SmcTuring.Native.SourceSeparation.guard_pointer_separate', 'SmcTuring.Native.SourceSeparation.pointer_offset_separate', 'SmcTuring.Native.SourceSeparation.pointer_mutable_separate', 'SmcTuring.Native.SourceSeparation.offset_fields_before', 'SmcTuring.Native.SourceSeparation.pointer_fields_before', 'SmcTuring.Native.SourceSeparation.pointer_control_separate', 'SmcTuring.Native.SourceSeparation.register_label_address_separate']
    assert set(native_source_separation_names) <= {item["name"] for item in declarations}
    report["native_source_separation_checked"] = True
    report["checked_native_source_separation_declarations"] = native_source_separation_names
    native_source_readiness_names = ['SmcTuring.Native.SourceReadiness.immediate_ready', 'SmcTuring.Native.SourceReadiness.address_ready', 'SmcTuring.Native.SourceReadiness.load_ready', 'SmcTuring.Native.SourceReadiness.store_ready', 'SmcTuring.Native.SourceReadiness.block_ready']
    assert set(native_source_readiness_names) <= {item["name"] for item in declarations}
    report["native_source_readiness_checked"] = True
    report["checked_native_source_readiness_declarations"] = native_source_readiness_names
    native_program_certificate_names = ['SmcTuring.Native.ProgramCertificate.pointer_layout', 'SmcTuring.Native.ProgramCertificate.source_setup', 'SmcTuring.Native.ProgramCertificate.end_word', 'SmcTuring.Native.ProgramCertificate.entry_word', 'SmcTuring.Native.ProgramCertificate.linked', 'SmcTuring.Native.ProgramCertificate.kernel_correct', 'SmcTuring.Native.ProgramCertificate.closed_pass_correct']
    assert set(native_program_certificate_names) <= {item["name"] for item in declarations}
    report["native_program_certificate_checked"] = True
    report["checked_native_program_certificate_declarations"] = native_program_certificate_names
    native_memory_region_names = ['SmcTuring.Native.MemoryRegion.agree_refl', 'SmcTuring.Native.MemoryRegion.agree_symm', 'SmcTuring.Native.MemoryRegion.agree_trans', 'SmcTuring.Native.MemoryRegion.contains_byte', 'SmcTuring.Native.MemoryRegion.bytes_agree', 'SmcTuring.Native.MemoryRegion.load_agree', 'SmcTuring.Native.MemoryRegion.put_bytes_agree', 'SmcTuring.Native.MemoryRegion.put_word_agree', 'SmcTuring.Native.MemoryRegion.put_word_outside', 'SmcTuring.Native.MemoryRegion.expanded_snapshot_agrees', 'SmcTuring.Native.MemoryRegion.snapshot_expand', 'SmcTuring.Native.MemoryRegion.store_agrees']
    assert set(native_memory_region_names) <= {item["name"] for item in declarations}
    report["native_memory_region_checked"] = True
    report["checked_native_memory_region_declarations"] = native_memory_region_names
    native_region_execution_names = ['SmcTuring.Native.RegionExecution.state_agree_refl', 'SmcTuring.Native.RegionExecution.execute_agrees', 'SmcTuring.Native.RegionExecution.write_address_agrees', 'SmcTuring.Native.RegionExecution.write_value_agrees', 'SmcTuring.Native.RegionExecution.fetch_agrees', 'SmcTuring.Native.RegionExecution.state_agree_symm', 'SmcTuring.Native.RegionExecution.read_address_agrees', 'SmcTuring.Native.RegionExecution.read_within_agrees', 'SmcTuring.Native.RegionExecution.fetch_within_agrees', 'SmcTuring.Native.RegionExecution.safe_agrees', 'SmcTuring.Native.RegionExecution.trace_agrees', 'SmcTuring.Native.RegionExecution.owned_run_agrees', 'SmcTuring.Native.RegionExecution.run_outside']
    assert set(native_region_execution_names) <= {item["name"] for item in declarations}
    report["native_region_execution_checked"] = True
    report["checked_native_region_execution_declarations"] = native_region_execution_names
    native_loaded_execution_names = ['SmcTuring.Native.LoadedExecution.snapshot_agrees', 'SmcTuring.Native.LoadedExecution.snapshot_expand', 'SmcTuring.Native.LoadedExecution.step_complete', 'SmcTuring.Native.LoadedExecution.step_sound', 'SmcTuring.Native.LoadedExecution.trace_complete', 'SmcTuring.Native.LoadedExecution.trace_sound']
    assert set(native_loaded_execution_names) <= {item["name"] for item in declarations}
    report["native_loaded_execution_checked"] = True
    report["checked_native_loaded_execution_declarations"] = native_loaded_execution_names
    native_finite_footprint_names = ['SmcTuring.Native.FiniteFootprint.join_left', 'SmcTuring.Native.FiniteFootprint.join_right', 'SmcTuring.Native.FiniteFootprint.contains_widen', 'SmcTuring.Native.FiniteFootprint.safe_widen', 'SmcTuring.Native.FiniteFootprint.safe_run_widen', 'SmcTuring.Native.FiniteFootprint.event_safe', 'SmcTuring.Native.FiniteFootprint.run_safe', 'SmcTuring.Native.FiniteFootprint.loaded_prefix']
    assert set(native_finite_footprint_names) <= {item["name"] for item in declarations}
    report["native_finite_footprint_checked"] = True
    report["checked_native_finite_footprint_declarations"] = native_finite_footprint_names
    native_program_loaded_names = ['SmcTuring.Native.ProgramLoaded.register_contained', 'SmcTuring.Native.ProgramLoaded.heap_contained', 'SmcTuring.Native.ProgramLoaded.represented_agrees', 'SmcTuring.Native.ProgramLoaded.kernel_prefix', 'SmcTuring.Native.ProgramLoaded.closed_prefix']
    assert set(native_program_loaded_names) <= {item["name"] for item in declarations}
    report["native_program_loaded_checked"] = True
    report["checked_native_program_loaded_declarations"] = native_program_loaded_names
    native_window_bounds_names = ['SmcTuring.Native.WindowBounds.contained_slice', 'SmcTuring.Native.WindowBounds.core_length_bound', 'SmcTuring.Native.WindowBounds.classified_length_bound', 'SmcTuring.Native.WindowBounds.fetch_within', 'SmcTuring.Native.WindowBounds.safe', 'SmcTuring.Native.WindowBounds.safe_run_append']
    assert set(native_window_bounds_names) <= {item["name"] for item in declarations}
    report["native_window_bounds_checked"] = True
    report["checked_native_window_bounds_declarations"] = native_window_bounds_names
    native_reader_bounds_names = ['SmcTuring.Native.ReaderBounds.label_contained', 'SmcTuring.Native.ReaderBounds.safe_run', 'SmcTuring.Native.ReaderBounds.loaded']
    assert set(native_reader_bounds_names) <= {item["name"] for item in declarations}
    report["native_reader_bounds_checked"] = True
    report["checked_native_reader_bounds_declarations"] = native_reader_bounds_names
    native_calls_bounds_names = ['SmcTuring.Native.CallsBounds.safe_run', 'SmcTuring.Native.CallsBounds.loaded']
    assert set(native_calls_bounds_names) <= {item["name"] for item in declarations}
    report["native_calls_bounds_checked"] = True
    report["checked_native_calls_bounds_declarations"] = native_calls_bounds_names
    native_read_callee_bounds_names = ['SmcTuring.Native.ReadCalleeBounds.safe_run', 'SmcTuring.Native.ReadCalleeBounds.loaded']
    assert set(native_read_callee_bounds_names) <= {item["name"] for item in declarations}
    report["native_read_callee_bounds_checked"] = True
    report["checked_native_read_callee_bounds_declarations"] = native_read_callee_bounds_names
    native_read_invocation_bounds_names = ['SmcTuring.Native.ReadInvocationBounds.safe_run', 'SmcTuring.Native.ReadInvocationBounds.loaded']
    assert set(native_read_invocation_bounds_names) <= {item["name"] for item in declarations}
    report["native_read_invocation_bounds_checked"] = True
    report["checked_native_read_invocation_bounds_declarations"] = native_read_invocation_bounds_names
    native_scalar_bounds_names = ['SmcTuring.Native.ScalarBounds.safe_run', 'SmcTuring.Native.ScalarBounds.loaded']
    assert set(native_scalar_bounds_names) <= {item["name"] for item in declarations}
    report["native_scalar_bounds_checked"] = True
    report["checked_native_scalar_bounds_declarations"] = native_scalar_bounds_names
    native_read_scalar_bounds_names = ['SmcTuring.Native.ReadScalarBounds.safe_run', 'SmcTuring.Native.ReadScalarBounds.loaded']
    assert set(native_read_scalar_bounds_names) <= {item["name"] for item in declarations}
    report["native_read_scalar_bounds_checked"] = True
    report["checked_native_read_scalar_bounds_declarations"] = native_read_scalar_bounds_names
    native_allocation_names = ['SmcTuring.Native.Allocation.origin_before_grid', 'SmcTuring.Native.Allocation.capacity', 'SmcTuring.Native.Allocation.control_limit', 'SmcTuring.Native.Allocation.entry_window', 'SmcTuring.Native.Allocation.snippet_bounds', 'SmcTuring.Native.Allocation.snippet_window', 'SmcTuring.Native.Allocation.operand_contained', 'SmcTuring.Native.Allocation.register_contained', 'SmcTuring.Native.Allocation.heap_contained', 'SmcTuring.Native.Allocation.reader_value_contained', 'SmcTuring.Native.Allocation.reader_window', 'SmcTuring.Native.Allocation.reader_invocation_safe', 'SmcTuring.Native.Allocation.reader_invocation_loaded', 'SmcTuring.Native.Allocation.destination_contained', 'SmcTuring.Native.Allocation.scalar_safe', 'SmcTuring.Native.Allocation.scalar_loaded', 'SmcTuring.Native.Allocation.read_scalar_safe', 'SmcTuring.Native.Allocation.read_scalar_loaded', 'SmcTuring.Native.Allocation.control_contained']
    assert set(native_allocation_names) <= {item["name"] for item in declarations}
    report["native_allocation_checked"] = True
    report["checked_native_allocation_declarations"] = native_allocation_names
    native_placed_bounds_names = ['SmcTuring.Native.PlacedBounds.snippet_bounds', 'SmcTuring.Native.PlacedBounds.snippet_window', 'SmcTuring.Native.PlacedBounds.entry_window', 'SmcTuring.Native.PlacedBounds.scalar_safe', 'SmcTuring.Native.PlacedBounds.calls_safe', 'SmcTuring.Native.PlacedBounds.reader_invocation_safe', 'SmcTuring.Native.PlacedBounds.read_scalar_safe', 'SmcTuring.Native.PlacedBounds.safe_trace_append']
    assert set(native_placed_bounds_names) <= {item["name"] for item in declarations}
    report["native_placed_bounds_checked"] = True
    report["checked_native_placed_bounds_declarations"] = native_placed_bounds_names
    native_borrow_mask_bounds_names = ['SmcTuring.Native.BorrowMaskBounds.safe_run', 'SmcTuring.Native.BorrowMaskBounds.loaded']
    assert set(native_borrow_mask_bounds_names) <= {item["name"] for item in declarations}
    report["native_borrow_mask_bounds_checked"] = True
    report["checked_native_borrow_mask_bounds_declarations"] = native_borrow_mask_bounds_names
    native_guard_setup_bounds_names = ['SmcTuring.Native.GuardSetupBounds.safe_run', 'SmcTuring.Native.GuardSetupBounds.loaded']
    assert set(native_guard_setup_bounds_names) <= {item["name"] for item in declarations}
    report["native_guard_setup_bounds_checked"] = True
    report["checked_native_guard_setup_bounds_declarations"] = native_guard_setup_bounds_names
    native_guard_selection_bounds_names = ['SmcTuring.Native.GuardSelectionBounds.safe_run', 'SmcTuring.Native.GuardSelectionBounds.loaded']
    assert set(native_guard_selection_bounds_names) <= {item["name"] for item in declarations}
    report["native_guard_selection_bounds_checked"] = True
    report["checked_native_guard_selection_bounds_declarations"] = native_guard_selection_bounds_names
    native_guard_bounds_names = ['SmcTuring.Native.GuardBounds.safe_run', 'SmcTuring.Native.GuardBounds.loaded']
    assert set(native_guard_bounds_names) <= {item["name"] for item in declarations}
    report["native_guard_bounds_checked"] = True
    report["checked_native_guard_bounds_declarations"] = native_guard_bounds_names
    native_guard_invocation_bounds_names = ['SmcTuring.Native.GuardInvocationBounds.safe_run', 'SmcTuring.Native.GuardInvocationBounds.loaded']
    assert set(native_guard_invocation_bounds_names) <= {item["name"] for item in declarations}
    report["native_guard_invocation_bounds_checked"] = True
    report["checked_native_guard_invocation_bounds_declarations"] = native_guard_invocation_bounds_names
    native_guard_allocation_names = ['SmcTuring.Native.GuardAllocation.safe_run', 'SmcTuring.Native.GuardAllocation.loaded', 'SmcTuring.Native.GuardAllocation.invocation_safe', 'SmcTuring.Native.GuardAllocation.invocation_loaded']
    assert set(native_guard_allocation_names) <= {item["name"] for item in declarations}
    report["native_guard_allocation_checked"] = True
    report["checked_native_guard_allocation_declarations"] = native_guard_allocation_names
    native_source_access_names = ['SmcTuring.Native.SourceAccess.guard_safe', 'SmcTuring.Native.SourceAccess.invocation_safe']
    assert set(native_source_access_names) <= {item["name"] for item in declarations}
    report["native_source_access_checked"] = True
    report["checked_native_source_access_declarations"] = native_source_access_names
    native_offset_guard_bounds_names = ['SmcTuring.Native.OffsetGuardBounds.safe_run', 'SmcTuring.Native.OffsetGuardBounds.loaded']
    assert set(native_offset_guard_bounds_names) <= {item["name"] for item in declarations}
    report["native_offset_guard_bounds_checked"] = True
    report["checked_native_offset_guard_bounds_declarations"] = native_offset_guard_bounds_names
    native_pointer_bounds_names = ['SmcTuring.Native.PointerBounds.safe_run', 'SmcTuring.Native.PointerBounds.loaded']
    assert set(native_pointer_bounds_names) <= {item["name"] for item in declarations}
    report["native_pointer_bounds_checked"] = True
    report["checked_native_pointer_bounds_declarations"] = native_pointer_bounds_names
    native_address_bounds_names = ['SmcTuring.Native.AddressBounds.safe_run', 'SmcTuring.Native.AddressBounds.loaded']
    assert set(native_address_bounds_names) <= {item["name"] for item in declarations}
    report["native_address_bounds_checked"] = True
    report["checked_native_address_bounds_declarations"] = native_address_bounds_names
    native_store_callee_bounds_names = ['SmcTuring.Native.StoreCalleeBounds.safe_run', 'SmcTuring.Native.StoreCalleeBounds.loaded']
    assert set(native_store_callee_bounds_names) <= {item["name"] for item in declarations}
    report["native_store_callee_bounds_checked"] = True
    report["checked_native_store_callee_bounds_declarations"] = native_store_callee_bounds_names
    native_store_invocation_bounds_names = ['SmcTuring.Native.StoreInvocationBounds.safe_run', 'SmcTuring.Native.StoreInvocationBounds.loaded']
    assert set(native_store_invocation_bounds_names) <= {item["name"] for item in declarations}
    report["native_store_invocation_bounds_checked"] = True
    report["checked_native_store_invocation_bounds_declarations"] = native_store_invocation_bounds_names
    native_immediate_bounds_names = ['SmcTuring.Native.ImmediateBounds.safe_run', 'SmcTuring.Native.ImmediateBounds.loaded']
    assert set(native_immediate_bounds_names) <= {item["name"] for item in declarations}
    report["native_immediate_bounds_checked"] = True
    report["checked_native_immediate_bounds_declarations"] = native_immediate_bounds_names
    native_load_bounds_names = ['SmcTuring.Native.LoadBounds.safe_run', 'SmcTuring.Native.LoadBounds.loaded']
    assert set(native_load_bounds_names) <= {item["name"] for item in declarations}
    report["native_load_bounds_checked"] = True
    report["checked_native_load_bounds_declarations"] = native_load_bounds_names
    native_store_bounds_names = ['SmcTuring.Native.StoreBounds.safe_run', 'SmcTuring.Native.StoreBounds.loaded']
    assert set(native_store_bounds_names) <= {item["name"] for item in declarations}
    report["native_store_bounds_checked"] = True
    report["checked_native_store_bounds_declarations"] = native_store_bounds_names
    native_block_bounds_names = ['SmcTuring.Native.BlockBounds.safe_run', 'SmcTuring.Native.BlockBounds.loaded']
    assert set(native_block_bounds_names) <= {item["name"] for item in declarations}
    report["native_block_bounds_checked"] = True
    report["checked_native_block_bounds_declarations"] = native_block_bounds_names
    native_source_allocation_names = ['SmcTuring.Native.SourceAllocation.data_within', 'SmcTuring.Native.SourceAllocation.guard_fields', 'SmcTuring.Native.SourceAllocation.block_static', 'SmcTuring.Native.SourceAllocation.block_safe', 'SmcTuring.Native.SourceAllocation.block_loaded']
    assert set(native_source_allocation_names) <= {item["name"] for item in declarations}
    report["native_source_allocation_checked"] = True
    report["checked_native_source_allocation_declarations"] = native_source_allocation_names
    native_program_bounds_names = ['SmcTuring.Native.ProgramBounds.safe_run', 'SmcTuring.Native.ProgramBounds.loaded']
    assert set(native_program_bounds_names) <= {item["name"] for item in declarations}
    report["native_program_bounds_checked"] = True
    report["checked_native_program_bounds_declarations"] = native_program_bounds_names
    native_program_allocation_names = ['SmcTuring.Native.ProgramAllocation.kernel_safe', 'SmcTuring.Native.ProgramAllocation.closed_safe', 'SmcTuring.Native.ProgramAllocation.kernel_loaded', 'SmcTuring.Native.ProgramAllocation.closed_loaded']
    assert set(native_program_allocation_names) <= {item["name"] for item in declarations}
    report["native_program_allocation_checked"] = True
    report["checked_native_program_allocation_declarations"] = native_program_allocation_names
    native_address_space_names = ['SmcTuring.Native.AddressSpace.region_valid', 'SmcTuring.Native.AddressSpace.contains_valid', 'SmcTuring.Native.AddressSpace.x86_fits', 'SmcTuring.Native.AddressSpace.x64_low_fits', 'SmcTuring.Native.AddressSpace.x64_high_fits', 'SmcTuring.Native.AddressSpace.x64_gap_invalid']
    assert set(native_address_space_names) <= {item["name"] for item in declarations}
    report["native_address_space_checked"] = True
    report["checked_native_address_space_declarations"] = native_address_space_names
    native_mapped_execution_names = ['SmcTuring.Native.MappedExecution.window_of_contains', 'SmcTuring.Native.MappedExecution.accesses_of_safe', 'SmcTuring.Native.MappedExecution.step_complete', 'SmcTuring.Native.MappedExecution.step_sound', 'SmcTuring.Native.MappedExecution.step_execute_denied', 'SmcTuring.Native.MappedExecution.step_invalid_pc', 'SmcTuring.Native.MappedExecution.trace_complete', 'SmcTuring.Native.MappedExecution.access_run_of_safe', 'SmcTuring.Native.MappedExecution.trace_loaded', 'SmcTuring.Native.MappedExecution.trace_sound']
    assert set(native_mapped_execution_names) <= {item["name"] for item in declarations}
    report["native_mapped_execution_checked"] = True
    report["checked_native_mapped_execution_declarations"] = native_mapped_execution_names
    native_program_mapped_names = ['SmcTuring.Native.ProgramMapped.mapped', 'SmcTuring.Native.ProgramMapped.x86_mapped', 'SmcTuring.Native.ProgramMapped.x64_low_mapped', 'SmcTuring.Native.ProgramMapped.x64_high_mapped', 'SmcTuring.Native.ProgramMapped.kernel_checked', 'SmcTuring.Native.ProgramMapped.closed_checked']
    assert set(native_program_mapped_names) <= {item["name"] for item in declarations}
    report["native_program_mapped_checked"] = True
    report["checked_native_program_mapped_declarations"] = native_program_mapped_names
    native_control_bounds_names = ['SmcTuring.Native.ControlBounds.pc_valid_of_safe', 'SmcTuring.Native.ControlBounds.targets_of_safe', 'SmcTuring.Native.ControlBounds.targets_of_trace']
    assert set(native_control_bounds_names) <= {item["name"] for item in declarations}
    report["native_control_bounds_checked"] = True
    report["checked_native_control_bounds_declarations"] = native_control_bounds_names
    native_program_control_names = ['SmcTuring.Native.ProgramControl.closed_targets', 'SmcTuring.Native.ProgramControl.closed_checked']
    assert set(native_program_control_names) <= {item["name"] for item in declarations}
    report["native_program_control_checked"] = True
    report["checked_native_program_control_declarations"] = native_program_control_names
    native_program_endpoint_names = ['SmcTuring.Native.ProgramEndpoint.failure_target', 'SmcTuring.Native.ProgramEndpoint.endpoint']
    assert set(native_program_endpoint_names) <= {item["name"] for item in declarations}
    report["native_program_endpoint_checked"] = True
    report["checked_native_program_endpoint_declarations"] = native_program_endpoint_names
    native_source_endpoint_names = ['SmcTuring.Native.SourceEndpoint.host_contained', 'SmcTuring.Native.SourceEndpoint.backedge_contained', 'SmcTuring.Native.SourceEndpoint.contained_word_valid', 'SmcTuring.Native.SourceEndpoint.terminal_word', 'SmcTuring.Native.SourceEndpoint.block_snapshot', 'SmcTuring.Native.SourceEndpoint.kernel_pc', 'SmcTuring.Native.SourceEndpoint.kernel_targets', 'SmcTuring.Native.SourceEndpoint.kernel_checked']
    assert set(native_source_endpoint_names) <= {item["name"] for item in declarations}
    report["native_source_endpoint_checked"] = True
    report["checked_native_source_endpoint_declarations"] = native_source_endpoint_names
    native_checked_execution_names = ['SmcTuring.Native.CheckedExecution.target_valid_agrees', 'SmcTuring.Native.CheckedExecution.step_complete', 'SmcTuring.Native.CheckedExecution.step_sound', 'SmcTuring.Native.CheckedExecution.step_target_denied', 'SmcTuring.Native.CheckedExecution.trace_complete', 'SmcTuring.Native.CheckedExecution.trace_loaded', 'SmcTuring.Native.CheckedExecution.trace_targets', 'SmcTuring.Native.CheckedExecution.trace_sound']
    assert set(native_checked_execution_names) <= {item["name"] for item in declarations}
    report["native_checked_execution_checked"] = True
    report["checked_native_checked_execution_declarations"] = native_checked_execution_names
    native_source_checked_names = ['SmcTuring.Native.SourceChecked.kernel', 'SmcTuring.Native.SourceChecked.closed']
    assert set(native_source_checked_names) <= {item["name"] for item in declarations}
    report["native_source_checked_checked"] = True
    report["checked_native_source_checked_declarations"] = native_source_checked_names
    native_loop_bounds_names = ['SmcTuring.Native.LoopBounds.pass_safe']
    assert set(native_loop_bounds_names) <= {item["name"] for item in declarations}
    report["native_loop_bounds_checked"] = True
    report["checked_native_loop_bounds_declarations"] = native_loop_bounds_names
    native_program_iteration_names = ['SmcTuring.Native.ProgramIteration.correct', 'SmcTuring.Native.ProgramIteration.accepted_length', 'SmcTuring.Native.ProgramIteration.targets']
    assert set(native_program_iteration_names) <= {item["name"] for item in declarations}
    report["native_program_iteration_checked"] = True
    report["checked_native_program_iteration_declarations"] = native_program_iteration_names
    native_source_iteration_names = ['SmcTuring.Native.SourceIteration.entry_contained', 'SmcTuring.Native.SourceIteration.static', 'SmcTuring.Native.SourceIteration.correct', 'SmcTuring.Native.SourceIteration.checked']
    assert set(native_source_iteration_names) <= {item["name"] for item in declarations}
    report["native_source_iteration_checked"] = True
    report["checked_native_source_iteration_declarations"] = native_source_iteration_names
    x64_half_words_names = ['SmcTuring.X64.HalfWords.low_pack', 'SmcTuring.X64.HalfWords.high_pack', 'SmcTuring.X64.HalfWords.pack_halves', 'SmcTuring.X64.HalfWords.split_xor', 'SmcTuring.X64.HalfWords.split_and', 'SmcTuring.X64.HalfWords.split_or', 'SmcTuring.X64.HalfWords.split_not', 'SmcTuring.X64.HalfWords.split_mov', 'SmcTuring.X64.HalfWords.broadcast_as_repeated', 'SmcTuring.X64.HalfWords.broadcast_xor', 'SmcTuring.X64.HalfWords.broadcast_and', 'SmcTuring.X64.HalfWords.broadcast_or', 'SmcTuring.X64.HalfWords.broadcast_mov', 'SmcTuring.X64.HalfWords.pack_toNat', 'SmcTuring.X64.HalfWords.add_carry', 'SmcTuring.X64.HalfWords.sub_borrow', 'SmcTuring.X64.HalfWords.split_add_no_carry', 'SmcTuring.X64.HalfWords.split_sub_no_borrow', 'SmcTuring.X64.HalfWords.split_add_counterexample', 'SmcTuring.X64.HalfWords.split_sub_counterexample', 'SmcTuring.X64.HalfWords.repeated_one_counterexample', 'SmcTuring.X64.HalfWords.repeated_masks']
    assert set(x64_half_words_names) <= {item["name"] for item in declarations}
    report["x64_half_words_checked"] = True
    report["checked_x64_half_words_declarations"] = x64_half_words_names
    x64_half_frame_names = ['SmcTuring.X64.HalfFrame.every_instruction_writes', 'SmcTuring.X64.HalfFrame.run_append', 'SmcTuring.X64.HalfFrame.pure_append', 'SmcTuring.X64.HalfFrame.restored_exchange', 'SmcTuring.X64.HalfFrame.carry_idempotent', 'SmcTuring.X64.HalfFrame.use_effect', 'SmcTuring.X64.HalfFrame.use_accumulator', 'SmcTuring.X64.HalfFrame.use_source', 'SmcTuring.X64.HalfFrame.use_target', 'SmcTuring.X64.HalfFrame.use_carry', 'SmcTuring.X64.HalfFrame.use_frame', 'SmcTuring.X64.HalfFrame.use_length', 'SmcTuring.X64.HalfFrame.use_pure', 'SmcTuring.X64.HalfFrame.split_effect', 'SmcTuring.X64.HalfFrame.split_accumulator', 'SmcTuring.X64.HalfFrame.split_sources', 'SmcTuring.X64.HalfFrame.split_carry', 'SmcTuring.X64.HalfFrame.split_frame', 'SmcTuring.X64.HalfFrame.split_length', 'SmcTuring.X64.HalfFrame.split_pure', 'SmcTuring.X64.HalfFrame.split_value', 'SmcTuring.X64.HalfFrame.split_correct', 'SmcTuring.X64.HalfFrame.complement_effect', 'SmcTuring.X64.HalfFrame.complement_correct', 'SmcTuring.X64.HalfFrame.complement_frame', 'SmcTuring.X64.HalfFrame.complement_registers', 'SmcTuring.X64.HalfFrame.complement_pure', 'SmcTuring.X64.HalfFrame.complement_length']
    assert set(x64_half_frame_names) <= {item["name"] for item in declarations}
    report["x64_half_frame_checked"] = True
    report["checked_x64_half_frame_declarations"] = x64_half_frame_names
    appendix_machine32_names = ['SmcTuring.Appendix.Machine32.every_instruction_writes', 'SmcTuring.Appendix.Machine32.execute_memory_frame', 'SmcTuring.Appendix.Machine32.run_append', 'SmcTuring.Appendix.Machine32.run_memory_frame', 'SmcTuring.Appendix.Machine32.pure_of_destinations']
    assert set(appendix_machine32_names) <= {item["name"] for item in declarations}
    report["appendix_machine32_checked"] = True
    report["checked_appendix_machine32_declarations"] = appendix_machine32_names
    appendix_branch_algebra_names = ['SmcTuring.Appendix.BranchAlgebra.flip_involution', 'SmcTuring.Appendix.BranchAlgebra.flip_injective', 'SmcTuring.Appendix.BranchAlgebra.one_bit_cases', 'SmcTuring.Appendix.BranchAlgebra.append_toNat', 'SmcTuring.Appendix.BranchAlgebra.flip_append', 'SmcTuring.Appendix.BranchAlgebra.flip_append_toNat', 'SmcTuring.Appendix.BranchAlgebra.flip_toNat', 'SmcTuring.Appendix.BranchAlgebra.flip_order', 'SmcTuring.Appendix.BranchAlgebra.normalized_eq', 'SmcTuring.Appendix.BranchAlgebra.difference_ne_zero', 'SmcTuring.Appendix.BranchAlgebra.raw_gt', 'SmcTuring.Appendix.BranchAlgebra.raw_ne', 'SmcTuring.Appendix.BranchAlgebra.all_relations', 'SmcTuring.Appendix.BranchAlgebra.sbb_mask', 'SmcTuring.Appendix.BranchAlgebra.complement_mask', 'SmcTuring.Appendix.BranchAlgebra.and_mask']
    assert set(appendix_branch_algebra_names) <= {item["name"] for item in declarations}
    report["appendix_branch_algebra_checked"] = True
    report["checked_appendix_branch_algebra_declarations"] = appendix_branch_algebra_names
    appendix_branching_names = ['SmcTuring.Appendix.Branching.comparison_accumulator', 'SmcTuring.Appendix.Branching.comparison_memory', 'SmcTuring.Appendix.Branching.accumulator', 'SmcTuring.Appendix.Branching.memory', 'SmcTuring.Appendix.Branching.carry', 'SmcTuring.Appendix.Branching.displacement', 'SmcTuring.Appendix.Branching.program_length', 'SmcTuring.Appendix.Branching.owned_destinations', 'SmcTuring.Appendix.Branching.pure', 'SmcTuring.Appendix.Branching.alias_counterexample', 'SmcTuring.Appendix.Branching.swap_separate', 'SmcTuring.Appendix.Branching.relation_memory', 'SmcTuring.Appendix.Branching.relation_displacement', 'SmcTuring.Appendix.Branching.relation_target', 'SmcTuring.Appendix.Branching.relation_accumulator', 'SmcTuring.Appendix.Branching.relation_carry', 'SmcTuring.Appendix.Branching.relation_frame', 'SmcTuring.Appendix.Branching.relation_pure']
    assert set(appendix_branching_names) <= {item["name"] for item in declarations}
    report["appendix_branching_checked"] = True
    report["checked_appendix_branching_declarations"] = appendix_branching_names
    appendix_branch_tail_names = ['SmcTuring.Appendix.BranchTail.tail_effect', 'SmcTuring.Appendix.BranchTail.tail_pc', 'SmcTuring.Appendix.BranchTail.tail_stack', 'SmcTuring.Appendix.BranchTail.tail_accumulator', 'SmcTuring.Appendix.BranchTail.tail_carry', 'SmcTuring.Appendix.BranchTail.tail_return', 'SmcTuring.Appendix.BranchTail.tail_frame', 'SmcTuring.Appendix.BranchTail.tail_pure', 'SmcTuring.Appendix.BranchTail.restore_effect', 'SmcTuring.Appendix.BranchTail.restore_accumulator', 'SmcTuring.Appendix.BranchTail.restore_frame', 'SmcTuring.Appendix.BranchTail.restoration_count', 'SmcTuring.Appendix.BranchTail.restoration_pure', 'SmcTuring.Appendix.BranchTail.continued_effect', 'SmcTuring.Appendix.BranchTail.continued_return', 'SmcTuring.Appendix.BranchTail.continued_frame', 'SmcTuring.Appendix.BranchTail.continued_alias', 'SmcTuring.Appendix.BranchTail.slot_add_no_carry', 'SmcTuring.Appendix.BranchTail.continued_alias_no_carry', 'SmcTuring.Appendix.BranchTail.prefixed_frame', 'SmcTuring.Appendix.BranchTail.branch_pc', 'SmcTuring.Appendix.BranchTail.branch_restored', 'SmcTuring.Appendix.BranchTail.branch_pure']
    assert set(appendix_branch_tail_names) <= {item["name"] for item in declarations}
    report["appendix_branch_tail_checked"] = True
    report["checked_appendix_branch_tail_declarations"] = appendix_branch_tail_names
    appendix_byte_code_names = ['SmcTuring.Appendix.ByteCode.immediate_tag', 'SmcTuring.Appendix.ByteCode.memory_tag', 'SmcTuring.Appendix.ByteCode.memory_not_immediate', 'SmcTuring.Appendix.ByteCode.immediate_payload', 'SmcTuring.Appendix.ByteCode.memory_payload', 'SmcTuring.Appendix.ByteCode.form_roundtrip', 'SmcTuring.Appendix.ByteCode.encode_injective', 'SmcTuring.Appendix.ByteCode.encode_length', 'SmcTuring.Appendix.ByteCode.length_bounds', 'SmcTuring.Appendix.ByteCode.encoded_length', 'SmcTuring.Appendix.ByteCode.length_take_two', 'SmcTuring.Appendix.ByteCode.fetch_current_encoding', 'SmcTuring.Appendix.ByteCode.fetch_written_encoding', 'SmcTuring.Appendix.ByteCode.immediate_patch', 'SmcTuring.Appendix.ByteCode.fetch_patched_immediate', 'SmcTuring.Appendix.ByteCode.fetch_patched_current_immediate', 'SmcTuring.Appendix.ByteCode.call_patch', 'SmcTuring.Appendix.ByteCode.fetch_patched_call', 'SmcTuring.Appendix.ByteCode.fetch_patched_current_call', 'SmcTuring.Appendix.ByteCode.put_bytes_append', 'SmcTuring.Appendix.ByteCode.patch_middle', 'SmcTuring.Appendix.ByteCode.address_patch', 'SmcTuring.Appendix.ByteCode.fetch_patched_address', 'SmcTuring.Appendix.ByteCode.fetch_patched_current_address']
    assert set(appendix_byte_code_names) <= {item["name"] for item in declarations}
    report["appendix_byte_code_checked"] = True
    report["checked_appendix_byte_code_declarations"] = appendix_byte_code_names
    appendix_byte_execution_names = ['SmcTuring.Appendix.ByteExecution.execute_effect', 'SmcTuring.Appendix.ByteExecution.execute_memory', 'SmcTuring.Appendix.ByteExecution.execute_accumulator', 'SmcTuring.Appendix.ByteExecution.execute_stack', 'SmcTuring.Appendix.ByteExecution.execute_carry', 'SmcTuring.Appendix.ByteExecution.execute_pc', 'SmcTuring.Appendix.ByteExecution.written_word', 'SmcTuring.Appendix.ByteExecution.execute_frame', 'SmcTuring.Appendix.ByteExecution.load_frame', 'SmcTuring.Appendix.ByteExecution.footprint_length', 'SmcTuring.Appendix.ByteExecution.footprint_nonempty', 'SmcTuring.Appendix.ByteExecution.store_preserves_carry', 'SmcTuring.Appendix.ByteExecution.xor_clears_carry', 'SmcTuring.Appendix.ByteExecution.and_clears_carry', 'SmcTuring.Appendix.ByteExecution.neg_carry', 'SmcTuring.Appendix.ByteExecution.not_preserves_carry', 'SmcTuring.Appendix.ByteExecution.sbb_value', 'SmcTuring.Appendix.ByteExecution.add_four_carry', 'SmcTuring.Appendix.ByteExecution.call_target', 'SmcTuring.Appendix.ByteExecution.call_return', 'SmcTuring.Appendix.ByteExecution.common_encoding', 'SmcTuring.Appendix.ByteExecution.common_execution', 'SmcTuring.Appendix.ByteExecution.step_current_encoding', 'SmcTuring.Appendix.ByteExecution.fetched_write', 'SmcTuring.Appendix.ByteExecution.step_patched_immediate', 'SmcTuring.Appendix.ByteExecution.step_patched_call', 'SmcTuring.Appendix.ByteExecution.step_patched_address', 'SmcTuring.Appendix.ByteExecution.trace_run', 'SmcTuring.Appendix.ByteExecution.run_append', 'SmcTuring.Appendix.ByteExecution.trace_append', 'SmcTuring.Appendix.ByteExecution.trace_head_step', 'SmcTuring.Appendix.ByteExecution.owned_append']
    assert set(appendix_byte_execution_names) <= {item["name"] for item in declarations}
    report["appendix_byte_execution_checked"] = True
    report["checked_appendix_byte_execution_declarations"] = appendix_byte_execution_names
    appendix_field_refinement_names = ['SmcTuring.Appendix.FieldRefinement.destination_dependency', 'SmcTuring.Appendix.FieldRefinement.address_toNat', 'SmcTuring.Appendix.FieldRefinement.equal_word_bytes', 'SmcTuring.Appendix.FieldRefinement.equal_word_byte', 'SmcTuring.Appendix.FieldRefinement.layout_outside', 'SmcTuring.Appendix.FieldRefinement.translate_destination', 'SmcTuring.Appendix.FieldRefinement.translate_value', 'SmcTuring.Appendix.FieldRefinement.translate_accumulator', 'SmcTuring.Appendix.FieldRefinement.translate_carry', 'SmcTuring.Appendix.FieldRefinement.translate_stack', 'SmcTuring.Appendix.FieldRefinement.execute_read_destination', 'SmcTuring.Appendix.FieldRefinement.execute_read_frame', 'SmcTuring.Appendix.FieldRefinement.simulate', 'SmcTuring.Appendix.FieldRefinement.forms_length', 'SmcTuring.Appendix.FieldRefinement.forms_run', 'SmcTuring.Appendix.FieldRefinement.simulate_run', 'SmcTuring.Appendix.FieldRefinement.run_stack', 'SmcTuring.Appendix.FieldRefinement.run_frame', 'SmcTuring.Appendix.FieldRefinement.owned_run', 'SmcTuring.Appendix.FieldRefinement.trace_refines']
    assert set(appendix_field_refinement_names) <= {item["name"] for item in declarations}
    report["appendix_field_refinement_checked"] = True
    report["checked_appendix_field_refinement_declarations"] = appendix_field_refinement_names
    appendix_branch_execution_names = ['SmcTuring.Appendix.BranchExecution.initial_agreement', 'SmcTuring.Appendix.BranchExecution.program_dependencies', 'SmcTuring.Appendix.BranchExecution.relation_dependencies', 'SmcTuring.Appendix.BranchExecution.refinement', 'SmcTuring.Appendix.BranchExecution.word_result', 'SmcTuring.Appendix.BranchExecution.displacement', 'SmcTuring.Appendix.BranchExecution.accumulator', 'SmcTuring.Appendix.BranchExecution.stack', 'SmcTuring.Appendix.BranchExecution.carry', 'SmcTuring.Appendix.BranchExecution.operand_x', 'SmcTuring.Appendix.BranchExecution.operand_y', 'SmcTuring.Appendix.BranchExecution.byte_frame', 'SmcTuring.Appendix.BranchExecution.restored_byte_frame', 'SmcTuring.Appendix.BranchExecution.owned', 'SmcTuring.Appendix.BranchExecution.modular_target', 'SmcTuring.Appendix.BranchExecution.trace_displacement']
    assert set(appendix_branch_execution_names) <= {item["name"] for item in declarations}
    report["appendix_branch_execution_checked"] = True
    report["checked_appendix_branch_execution_declarations"] = appendix_branch_execution_names
    appendix_byte_image_names = ['SmcTuring.Appendix.ByteImage.word_at_total', 'SmcTuring.Appendix.ByteImage.word_at_window', 'SmcTuring.Appendix.ByteImage.word_at_read_field', 'SmcTuring.Appendix.ByteImage.bytes_at_drop', 'SmcTuring.Appendix.ByteImage.payload_window', 'SmcTuring.Appendix.ByteImage.initial_length', 'SmcTuring.Appendix.ByteImage.current_length', 'SmcTuring.Appendix.ByteImage.immediate_words', 'SmcTuring.Appendix.ByteImage.relative_word', 'SmcTuring.Appendix.ByteImage.intact_current', 'SmcTuring.Appendix.ByteImage.fetch_current', 'SmcTuring.Appendix.ByteImage.initialized_packet', 'SmcTuring.Appendix.ByteImage.patch_owner', 'SmcTuring.Appendix.ByteImage.owned_field_inside', 'SmcTuring.Appendix.ByteImage.separated_tail', 'SmcTuring.Appendix.ByteImage.apart_bytes', 'SmcTuring.Appendix.ByteImage.image_packet', 'SmcTuring.Appendix.ByteImage.initialized_intact', 'SmcTuring.Appendix.ByteImage.frame_packet', 'SmcTuring.Appendix.ByteImage.store_intact', 'SmcTuring.Appendix.ByteImage.execute_intact']
    assert set(appendix_byte_image_names) <= {item["name"] for item in declarations}
    report["appendix_byte_image_checked"] = True
    report["checked_appendix_byte_image_declarations"] = appendix_byte_image_names
    appendix_byte_packing_names = ['SmcTuring.Appendix.BytePacking.size_cons', 'SmcTuring.Appendix.BytePacking.size_append', 'SmcTuring.Appendix.BytePacking.place_append', 'SmcTuring.Appendix.BytePacking.placed_lower', 'SmcTuring.Appendix.BytePacking.placed_upper', 'SmcTuring.Appendix.BytePacking.placed_separated', 'SmcTuring.Appendix.BytePacking.initial_intact', 'SmcTuring.Appendix.BytePacking.initial_fetch', 'SmcTuring.Appendix.BytePacking.fields_owned', 'SmcTuring.Appendix.BytePacking.same_owner_separate', 'SmcTuring.Appendix.BytePacking.owned_separate', 'SmcTuring.Appendix.BytePacking.field_layout', 'SmcTuring.Appendix.BytePacking.placed_field_layout', 'SmcTuring.Appendix.BytePacking.image_frame']
    assert set(appendix_byte_packing_names) <= {item["name"] for item in declarations}
    report["appendix_byte_packing_checked"] = True
    report["checked_appendix_byte_packing_declarations"] = appendix_byte_packing_names
    appendix_byte_program_names = ['SmcTuring.Appendix.ByteProgram.span_cons', 'SmcTuring.Appendix.ByteProgram.instruction_length', 'SmcTuring.Appendix.ByteProgram.current_translation', 'SmcTuring.Appendix.ByteProgram.execute_pc', 'SmcTuring.Appendix.ByteProgram.constructed_trace', 'SmcTuring.Appendix.ByteProgram.image_trace', 'SmcTuring.Appendix.ByteProgram.run_pc']
    assert set(appendix_byte_program_names) <= {item["name"] for item in declarations}
    report["appendix_byte_program_checked"] = True
    report["checked_appendix_byte_program_declarations"] = appendix_byte_program_names
    appendix_branch_layout_names = ['SmcTuring.Appendix.BranchLayout.span', 'SmcTuring.Appendix.BranchLayout.tail_size', 'SmcTuring.Appendix.BranchLayout.continuation_size', 'SmcTuring.Appendix.BranchLayout.image_end', 'SmcTuring.Appendix.BranchLayout.linked', 'SmcTuring.Appendix.BranchLayout.image_fields', 'SmcTuring.Appendix.BranchLayout.separate_fields', 'SmcTuring.Appendix.BranchLayout.fields_owned', 'SmcTuring.Appendix.BranchLayout.field_layout']
    assert set(appendix_branch_layout_names) <= {item["name"] for item in declarations}
    report["appendix_branch_layout_checked"] = True
    report["checked_appendix_branch_layout_declarations"] = appendix_branch_layout_names
    appendix_branch_prefix_names = ['SmcTuring.Appendix.BranchPrefix.prefix_placed', 'SmcTuring.Appendix.BranchPrefix.storage_placed', 'SmcTuring.Appendix.BranchPrefix.initial_operands', 'SmcTuring.Appendix.BranchPrefix.prefix_capacity', 'SmcTuring.Appendix.BranchPrefix.trace', 'SmcTuring.Appendix.BranchPrefix.finish_pc', 'SmcTuring.Appendix.BranchPrefix.displacement', 'SmcTuring.Appendix.BranchPrefix.initialized_displacement', 'SmcTuring.Appendix.BranchPrefix.accumulator', 'SmcTuring.Appendix.BranchPrefix.stack', 'SmcTuring.Appendix.BranchPrefix.carry', 'SmcTuring.Appendix.BranchPrefix.byte_frame', 'SmcTuring.Appendix.BranchPrefix.finish_intact']
    assert set(appendix_branch_prefix_names) <= {item["name"] for item in declarations}
    report["appendix_branch_prefix_checked"] = True
    report["checked_appendix_branch_prefix_declarations"] = appendix_branch_prefix_names
    appendix_byte_control_names = ['SmcTuring.Appendix.ByteControl.apart_symmetric', 'SmcTuring.Appendix.ByteControl.load_put', 'SmcTuring.Appendix.ByteControl.load_frame', 'SmcTuring.Appendix.ByteControl.put_overwrite', 'SmcTuring.Appendix.ByteControl.put_commute', 'SmcTuring.Appendix.ByteControl.put_back', 'SmcTuring.Appendix.ByteControl.exchange_stack_effect', 'SmcTuring.Appendix.ByteControl.exchange_acc_effect', 'SmcTuring.Appendix.ByteControl.add_four_effect', 'SmcTuring.Appendix.ByteControl.store_acc_effect', 'SmcTuring.Appendix.ByteControl.restore_run', 'SmcTuring.Appendix.ByteControl.restore_effect', 'SmcTuring.Appendix.ByteControl.call_effect', 'SmcTuring.Appendix.ByteControl.tail_run', 'SmcTuring.Appendix.ByteControl.tail_effect', 'SmcTuring.Appendix.ByteControl.continued_alias']
    assert set(appendix_byte_control_names) <= {item["name"] for item in declarations}
    report["appendix_byte_control_checked"] = True
    report["checked_appendix_byte_control_declarations"] = appendix_byte_control_names
    appendix_byte_linear_names = ['SmcTuring.Appendix.ByteLinear.span_cons', 'SmcTuring.Appendix.ByteLinear.minimum_length', 'SmcTuring.Appendix.ByteLinear.execute_pc', 'SmcTuring.Appendix.ByteLinear.constructed_trace', 'SmcTuring.Appendix.ByteLinear.image_trace', 'SmcTuring.Appendix.ByteLinear.run_pc', 'SmcTuring.Appendix.ByteLinear.owned_run', 'SmcTuring.Appendix.ByteLinear.run_intact']
    assert set(appendix_byte_linear_names) <= {item["name"] for item in declarations}
    report["appendix_byte_linear_checked"] = True
    report["checked_appendix_byte_linear_declarations"] = appendix_byte_linear_names
    appendix_branch_control_names = ['SmcTuring.Appendix.BranchControl.full_layout', 'SmcTuring.Appendix.BranchControl.field_owned', 'SmcTuring.Appendix.BranchControl.slot_apart', 'SmcTuring.Appendix.BranchControl.call_apart', 'SmcTuring.Appendix.BranchControl.slot_alias', 'SmcTuring.Appendix.BranchControl.pointer_nonwrap', 'SmcTuring.Appendix.BranchControl.stack_placed', 'SmcTuring.Appendix.BranchControl.initial_stack', 'SmcTuring.Appendix.BranchControl.prefix_load_frame', 'SmcTuring.Appendix.BranchControl.prefix_stack']
    assert set(appendix_branch_control_names) <= {item["name"] for item in declarations}
    report["appendix_branch_control_checked"] = True
    report["checked_appendix_branch_control_declarations"] = appendix_branch_control_names
    appendix_branch_paths_names = ['SmcTuring.Appendix.BranchPaths.tail_placed', 'SmcTuring.Appendix.BranchPaths.fall_placed', 'SmcTuring.Appendix.BranchPaths.taken_placed', 'SmcTuring.Appendix.BranchPaths.fetched_current', 'SmcTuring.Appendix.BranchPaths.tail_trace_intact']
    assert set(appendix_branch_paths_names) <= {item["name"] for item in declarations}
    report["appendix_branch_paths_checked"] = True
    report["checked_appendix_branch_paths_declarations"] = appendix_branch_paths_names
    appendix_branch_whole_names = ['SmcTuring.Appendix.BranchWhole.run_forms', 'SmcTuring.Appendix.BranchWhole.tail_pc', 'SmcTuring.Appendix.BranchWhole.restored', 'SmcTuring.Appendix.BranchWhole.finish_pc', 'SmcTuring.Appendix.BranchWhole.accumulator', 'SmcTuring.Appendix.BranchWhole.stack', 'SmcTuring.Appendix.BranchWhole.carry', 'SmcTuring.Appendix.BranchWhole.byte_frame', 'SmcTuring.Appendix.BranchWhole.continuation_ownership', 'SmcTuring.Appendix.BranchWhole.continuation_straight', 'SmcTuring.Appendix.BranchWhole.continuation_span', 'SmcTuring.Appendix.BranchWhole.continuation_trace', 'SmcTuring.Appendix.BranchWhole.trace', 'SmcTuring.Appendix.BranchWhole.tail_owned_run', 'SmcTuring.Appendix.BranchWhole.owned_run', 'SmcTuring.Appendix.BranchWhole.finish_intact', 'SmcTuring.Appendix.BranchWhole.correct']
    assert set(appendix_branch_whole_names) <= {item["name"] for item in declarations}
    report["appendix_branch_whole_checked"] = True
    report["checked_appendix_branch_whole_declarations"] = appendix_branch_whole_names
    appendix_byte_regions_names = ['SmcTuring.Appendix.ByteRegions.member', 'SmcTuring.Appendix.ByteRegions.entry_bounds', 'SmcTuring.Appendix.ByteRegions.separated_append', 'SmcTuring.Appendix.ByteRegions.separated', 'SmcTuring.Appendix.ByteRegions.capacity', 'SmcTuring.Appendix.ByteRegions.field_layout', 'SmcTuring.Appendix.ByteRegions.initial_intact', 'SmcTuring.Appendix.ByteRegions.image_append', 'SmcTuring.Appendix.ByteRegions.image_frame', 'SmcTuring.Appendix.ByteRegions.outside_owned']
    assert set(appendix_byte_regions_names) <= {item["name"] for item in declarations}
    report["appendix_byte_regions_checked"] = True
    report["checked_appendix_byte_regions_declarations"] = appendix_byte_regions_names
    appendix_spaced_layout_names = ['SmcTuring.Appendix.SpacedLayout.span', 'SmcTuring.Appendix.SpacedLayout.stack_size', 'SmcTuring.Appendix.SpacedLayout.storage_size', 'SmcTuring.Appendix.SpacedLayout.core_end', 'SmcTuring.Appendix.SpacedLayout.ordered', 'SmcTuring.Appendix.SpacedLayout.region_capacity', 'SmcTuring.Appendix.SpacedLayout.separated', 'SmcTuring.Appendix.SpacedLayout.image_fields', 'SmcTuring.Appendix.SpacedLayout.full_layout', 'SmcTuring.Appendix.SpacedLayout.field_owned', 'SmcTuring.Appendix.SpacedLayout.fields_owned', 'SmcTuring.Appendix.SpacedLayout.field_layout', 'SmcTuring.Appendix.SpacedLayout.linked', 'SmcTuring.Appendix.SpacedLayout.separate_fields', 'SmcTuring.Appendix.SpacedLayout.initial_intact', 'SmcTuring.Appendix.SpacedLayout.core_placed', 'SmcTuring.Appendix.SpacedLayout.stack_placed', 'SmcTuring.Appendix.SpacedLayout.prefix_placed', 'SmcTuring.Appendix.SpacedLayout.tail_placed', 'SmcTuring.Appendix.SpacedLayout.fall_placed', 'SmcTuring.Appendix.SpacedLayout.taken_placed', 'SmcTuring.Appendix.SpacedLayout.storage_placed', 'SmcTuring.Appendix.SpacedLayout.gap_frame', 'SmcTuring.Appendix.SpacedLayout.gap_outside', 'SmcTuring.Appendix.SpacedLayout.initial_gap_frame']
    assert set(appendix_spaced_layout_names) <= {item["name"] for item in declarations}
    report["appendix_spaced_layout_checked"] = True
    report["checked_appendix_spaced_layout_declarations"] = appendix_spaced_layout_names
    appendix_spaced_prefix_names = ['SmcTuring.Appendix.SpacedPrefix.initial_operands', 'SmcTuring.Appendix.SpacedPrefix.prefix_valid', 'SmcTuring.Appendix.SpacedPrefix.trace', 'SmcTuring.Appendix.SpacedPrefix.finish_pc', 'SmcTuring.Appendix.SpacedPrefix.displacement', 'SmcTuring.Appendix.SpacedPrefix.initialized_displacement', 'SmcTuring.Appendix.SpacedPrefix.accumulator', 'SmcTuring.Appendix.SpacedPrefix.stack', 'SmcTuring.Appendix.SpacedPrefix.carry', 'SmcTuring.Appendix.SpacedPrefix.byte_frame', 'SmcTuring.Appendix.SpacedPrefix.finish_intact']
    assert set(appendix_spaced_prefix_names) <= {item["name"] for item in declarations}
    report["appendix_spaced_prefix_checked"] = True
    report["checked_appendix_spaced_prefix_declarations"] = appendix_spaced_prefix_names
    appendix_spaced_control_names = ['SmcTuring.Appendix.SpacedControl.slot_apart', 'SmcTuring.Appendix.SpacedControl.call_apart', 'SmcTuring.Appendix.SpacedControl.slot_alias', 'SmcTuring.Appendix.SpacedControl.pointer_nonwrap', 'SmcTuring.Appendix.SpacedControl.initial_stack', 'SmcTuring.Appendix.SpacedControl.prefix_load_frame', 'SmcTuring.Appendix.SpacedControl.prefix_stack']
    assert set(appendix_spaced_control_names) <= {item["name"] for item in declarations}
    report["appendix_spaced_control_checked"] = True
    report["checked_appendix_spaced_control_declarations"] = appendix_spaced_control_names
    appendix_spaced_paths_names = ['SmcTuring.Appendix.SpacedPaths.tail_trace_intact']
    assert set(appendix_spaced_paths_names) <= {item["name"] for item in declarations}
    report["appendix_spaced_paths_checked"] = True
    report["checked_appendix_spaced_paths_declarations"] = appendix_spaced_paths_names
    appendix_spaced_whole_names = ['SmcTuring.Appendix.SpacedWhole.run_forms', 'SmcTuring.Appendix.SpacedWhole.tail_pc', 'SmcTuring.Appendix.SpacedWhole.restored', 'SmcTuring.Appendix.SpacedWhole.finish_pc', 'SmcTuring.Appendix.SpacedWhole.accumulator', 'SmcTuring.Appendix.SpacedWhole.stack', 'SmcTuring.Appendix.SpacedWhole.carry', 'SmcTuring.Appendix.SpacedWhole.byte_frame', 'SmcTuring.Appendix.SpacedWhole.continuation_ownership', 'SmcTuring.Appendix.SpacedWhole.continuation_straight', 'SmcTuring.Appendix.SpacedWhole.continuation_span', 'SmcTuring.Appendix.SpacedWhole.continuation_trace', 'SmcTuring.Appendix.SpacedWhole.trace', 'SmcTuring.Appendix.SpacedWhole.tail_owned_run', 'SmcTuring.Appendix.SpacedWhole.owned_run', 'SmcTuring.Appendix.SpacedWhole.finish_intact', 'SmcTuring.Appendix.SpacedWhole.correct', 'SmcTuring.Appendix.SpacedWhole.gap_frame']
    assert set(appendix_spaced_whole_names) <= {item["name"] for item in declarations}
    report["appendix_spaced_whole_checked"] = True
    report["checked_appendix_spaced_whole_declarations"] = appendix_spaced_whole_names
    appendix_multiply_control_names = ['SmcTuring.Appendix.MultiplyControl.run_append', 'SmcTuring.Appendix.MultiplyControl.pure_append', 'SmcTuring.Appendix.MultiplyControl.lift_effect', 'SmcTuring.Appendix.MultiplyControl.lift_pure', 'SmcTuring.Appendix.MultiplyControl.literal_lengths', 'SmcTuring.Appendix.MultiplyControl.tail_effect', 'SmcTuring.Appendix.MultiplyControl.restore_effect', 'SmcTuring.Appendix.MultiplyControl.round_trip_effect', 'SmcTuring.Appendix.MultiplyControl.round_trip_ready', 'SmcTuring.Appendix.MultiplyControl.round_trip_pure', 'SmcTuring.Appendix.MultiplyControl.guard_ignore_carry', 'SmcTuring.Appendix.MultiplyControl.loop_ignore_carry', 'SmcTuring.Appendix.MultiplyControl.clear_carry_memory', 'SmcTuring.Appendix.MultiplyControl.lift_length']
    assert set(appendix_multiply_control_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_control_checked"] = True
    report["checked_appendix_multiply_control_declarations"] = appendix_multiply_control_names
    appendix_multiply_blocks_names = ['SmcTuring.Appendix.MultiplyBlocks.delta_value', 'SmcTuring.Appendix.MultiplyBlocks.delta_nonzero', 'SmcTuring.Appendix.MultiplyBlocks.continuations_distinct', 'SmcTuring.Appendix.MultiplyBlocks.words_pure', 'SmcTuring.Appendix.MultiplyBlocks.words_frame', 'SmcTuring.Appendix.MultiplyBlocks.ready_lift', 'SmcTuring.Appendix.MultiplyBlocks.call_separate', 'SmcTuring.Appendix.MultiplyBlocks.program_effect', 'SmcTuring.Appendix.MultiplyBlocks.program_ready', 'SmcTuring.Appendix.MultiplyBlocks.program_frame', 'SmcTuring.Appendix.MultiplyBlocks.program_pure', 'SmcTuring.Appendix.MultiplyBlocks.clear_guard', 'SmcTuring.Appendix.MultiplyBlocks.guard_effect', 'SmcTuring.Appendix.MultiplyBlocks.body_effect', 'SmcTuring.Appendix.MultiplyBlocks.entry_effect', 'SmcTuring.Appendix.MultiplyBlocks.finish_effect']
    assert set(appendix_multiply_blocks_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_blocks_checked"] = True
    report["checked_appendix_multiply_blocks_declarations"] = appendix_multiply_blocks_names
    appendix_multiply_execution_names = ['SmcTuring.Appendix.MultiplyExecution.exit_matches', 'SmcTuring.Appendix.MultiplyExecution.loop_matches', 'SmcTuring.Appendix.MultiplyExecution.loop_run', 'SmcTuring.Appendix.MultiplyExecution.loop_pure', 'SmcTuring.Appendix.MultiplyExecution.correct']
    assert set(appendix_multiply_execution_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_execution_checked"] = True
    report["checked_appendix_multiply_execution_declarations"] = appendix_multiply_execution_names
    appendix_multiply_loop_names = ['SmcTuring.Appendix.MultiplyLoop.guard_invariant', 'SmcTuring.Appendix.MultiplyLoop.body_invariant', 'SmcTuring.Appendix.MultiplyLoop.exit_post', 'SmcTuring.Appendix.MultiplyLoop.post_step', 'SmcTuring.Appendix.MultiplyLoop.loop_correct', 'SmcTuring.Appendix.MultiplyLoop.loop_run', 'SmcTuring.Appendix.MultiplyLoop.pure_append', 'SmcTuring.Appendix.MultiplyLoop.loop_pure', 'SmcTuring.Appendix.MultiplyLoop.full_product', 'SmcTuring.Appendix.MultiplyLoop.multiply_run', 'SmcTuring.Appendix.MultiplyLoop.multiply_pure', 'SmcTuring.Appendix.MultiplyLoop.pure_destinations', 'SmcTuring.Appendix.MultiplyLoop.multiply_frame', 'SmcTuring.Appendix.MultiplyLoop.loop_length', 'SmcTuring.Appendix.MultiplyLoop.multiply_length']
    assert set(appendix_multiply_loop_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_loop_checked"] = True
    report["checked_appendix_multiply_loop_declarations"] = appendix_multiply_loop_names
    appendix_multiply_words_names = ['SmcTuring.Appendix.MultiplyWords.full_and', 'SmcTuring.Appendix.MultiplyWords.and_full', 'SmcTuring.Appendix.MultiplyWords.field_eq', 'SmcTuring.Appendix.MultiplyWords.every_instruction_writes', 'SmcTuring.Appendix.MultiplyWords.execute_frame', 'SmcTuring.Appendix.MultiplyWords.run_frame', 'SmcTuring.Appendix.MultiplyWords.run_append', 'SmcTuring.Appendix.MultiplyWords.pure_of_destinations', 'SmcTuring.Appendix.MultiplyWords.copy_effect', 'SmcTuring.Appendix.MultiplyWords.initialize_field', 'SmcTuring.Appendix.MultiplyWords.initialize_accumulator', 'SmcTuring.Appendix.MultiplyWords.initialize_carry', 'SmcTuring.Appendix.MultiplyWords.guard_field', 'SmcTuring.Appendix.MultiplyWords.guard_accumulator', 'SmcTuring.Appendix.MultiplyWords.guard_carry', 'SmcTuring.Appendix.MultiplyWords.guard_displacement', 'SmcTuring.Appendix.MultiplyWords.guard_target', 'SmcTuring.Appendix.MultiplyWords.body_field', 'SmcTuring.Appendix.MultiplyWords.body_accumulator', 'SmcTuring.Appendix.MultiplyWords.body_carry', 'SmcTuring.Appendix.MultiplyWords.body_frame', 'SmcTuring.Appendix.MultiplyWords.finish_field', 'SmcTuring.Appendix.MultiplyWords.finish_registers', 'SmcTuring.Appendix.MultiplyWords.initialize_pure', 'SmcTuring.Appendix.MultiplyWords.guard_pure', 'SmcTuring.Appendix.MultiplyWords.body_pure', 'SmcTuring.Appendix.MultiplyWords.finish_pure', 'SmcTuring.Appendix.MultiplyWords.block_lengths']
    assert set(appendix_multiply_words_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_words_checked"] = True
    report["checked_appendix_multiply_words_declarations"] = appendix_multiply_words_names
    appendix_multiply_algebra_names = ['SmcTuring.Appendix.MultiplyAlgebra.low_bit_toNat', 'SmcTuring.Appendix.MultiplyAlgebra.low_bit_cases', 'SmcTuring.Appendix.MultiplyAlgebra.shifted_toNat', 'SmcTuring.Appendix.MultiplyAlgebra.doubled', 'SmcTuring.Appendix.MultiplyAlgebra.decomposition', 'SmcTuring.Appendix.MultiplyAlgebra.chosen_product', 'SmcTuring.Appendix.MultiplyAlgebra.step_invariant', 'SmcTuring.Appendix.MultiplyAlgebra.shifted_bound', 'SmcTuring.Appendix.MultiplyAlgebra.iterate_correct', 'SmcTuring.Appendix.MultiplyAlgebra.full_word_product']
    assert set(appendix_multiply_algebra_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_algebra_checked"] = True
    report["checked_appendix_multiply_algebra_declarations"] = appendix_multiply_algebra_names


    appendix_multiply_byte_code_names = ['SmcTuring.Appendix.MultiplyByteCode.common_decode', 'SmcTuring.Appendix.MultiplyByteCode.add_payload', 'SmcTuring.Appendix.MultiplyByteCode.form_roundtrip', 'SmcTuring.Appendix.MultiplyByteCode.encode_injective', 'SmcTuring.Appendix.MultiplyByteCode.encode_length', 'SmcTuring.Appendix.MultiplyByteCode.length_bounds', 'SmcTuring.Appendix.MultiplyByteCode.common_length', 'SmcTuring.Appendix.MultiplyByteCode.encoded_length', 'SmcTuring.Appendix.MultiplyByteCode.length_take_two', 'SmcTuring.Appendix.MultiplyByteCode.fetch_current_encoding', 'SmcTuring.Appendix.MultiplyByteCode.fetch_written_encoding', 'SmcTuring.Appendix.MultiplyByteCode.add_patch', 'SmcTuring.Appendix.MultiplyByteCode.fetch_patched_add', 'SmcTuring.Appendix.MultiplyByteCode.fetch_patched_current_add']
    assert set(appendix_multiply_byte_code_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_code_checked"] = True
    report["checked_appendix_multiply_byte_code_declarations"] = appendix_multiply_byte_code_names

    appendix_multiply_byte_execution_names = ['SmcTuring.Appendix.MultiplyByteExecution.execute_effect', 'SmcTuring.Appendix.MultiplyByteExecution.execute_memory', 'SmcTuring.Appendix.MultiplyByteExecution.execute_accumulator', 'SmcTuring.Appendix.MultiplyByteExecution.execute_stack', 'SmcTuring.Appendix.MultiplyByteExecution.execute_carry', 'SmcTuring.Appendix.MultiplyByteExecution.execute_pc', 'SmcTuring.Appendix.MultiplyByteExecution.written_word', 'SmcTuring.Appendix.MultiplyByteExecution.execute_frame', 'SmcTuring.Appendix.MultiplyByteExecution.load_frame', 'SmcTuring.Appendix.MultiplyByteExecution.footprint_length', 'SmcTuring.Appendix.MultiplyByteExecution.footprint_nonempty', 'SmcTuring.Appendix.MultiplyByteExecution.common_execution', 'SmcTuring.Appendix.MultiplyByteExecution.and_native_encoding', 'SmcTuring.Appendix.MultiplyByteExecution.and_native_execution', 'SmcTuring.Appendix.MultiplyByteExecution.and_clears_carry', 'SmcTuring.Appendix.MultiplyByteExecution.add_carry', 'SmcTuring.Appendix.MultiplyByteExecution.shift_left_carry', 'SmcTuring.Appendix.MultiplyByteExecution.shift_right_carry', 'SmcTuring.Appendix.MultiplyByteExecution.step_current_encoding', 'SmcTuring.Appendix.MultiplyByteExecution.step_patched_add', 'SmcTuring.Appendix.MultiplyByteExecution.trace_run', 'SmcTuring.Appendix.MultiplyByteExecution.run_append', 'SmcTuring.Appendix.MultiplyByteExecution.trace_append', 'SmcTuring.Appendix.MultiplyByteExecution.owned_append']
    assert set(appendix_multiply_byte_execution_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_execution_checked"] = True
    report["checked_appendix_multiply_byte_execution_declarations"] = appendix_multiply_byte_execution_names

    appendix_multiply_refinement_names = ['SmcTuring.Appendix.MultiplyRefinement.destination_dependency', 'SmcTuring.Appendix.MultiplyRefinement.translate_destination', 'SmcTuring.Appendix.MultiplyRefinement.translate_value', 'SmcTuring.Appendix.MultiplyRefinement.translate_accumulator', 'SmcTuring.Appendix.MultiplyRefinement.translate_carry', 'SmcTuring.Appendix.MultiplyRefinement.translate_stack', 'SmcTuring.Appendix.MultiplyRefinement.translate_length', 'SmcTuring.Appendix.MultiplyRefinement.execute_pc', 'SmcTuring.Appendix.MultiplyRefinement.execute_read_destination', 'SmcTuring.Appendix.MultiplyRefinement.execute_read_frame', 'SmcTuring.Appendix.MultiplyRefinement.simulate', 'SmcTuring.Appendix.MultiplyRefinement.forms_length', 'SmcTuring.Appendix.MultiplyRefinement.forms_run', 'SmcTuring.Appendix.MultiplyRefinement.simulate_run', 'SmcTuring.Appendix.MultiplyRefinement.run_stack', 'SmcTuring.Appendix.MultiplyRefinement.run_frame', 'SmcTuring.Appendix.MultiplyRefinement.owned_run']
    assert set(appendix_multiply_refinement_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_refinement_checked"] = True
    report["checked_appendix_multiply_refinement_declarations"] = appendix_multiply_refinement_names

    appendix_multiply_packets_names = ['SmcTuring.Appendix.MultiplyPackets.literal_current', 'SmcTuring.Appendix.MultiplyPackets.literal_length', 'SmcTuring.Appendix.MultiplyPackets.data_lengths', 'SmcTuring.Appendix.MultiplyPackets.tail_span', 'SmcTuring.Appendix.MultiplyPackets.restore_span', 'SmcTuring.Appendix.MultiplyPackets.packet_count', 'SmcTuring.Appendix.MultiplyPackets.data_lengths_block', 'SmcTuring.Appendix.MultiplyPackets.packet_lengths', 'SmcTuring.Appendix.MultiplyPackets.packet_span', 'SmcTuring.Appendix.MultiplyPackets.positioned_offsets', 'SmcTuring.Appendix.MultiplyPackets.packet_offsets', 'SmcTuring.Appendix.MultiplyPackets.owner_coordinates', 'SmcTuring.Appendix.MultiplyPackets.stack_alias', 'SmcTuring.Appendix.MultiplyPackets.inactive_count', 'SmcTuring.Appendix.MultiplyPackets.inactive_span']
    assert set(appendix_multiply_packets_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_packets_checked"] = True
    report["checked_appendix_multiply_packets_declarations"] = appendix_multiply_packets_names

    appendix_multiply_image_names = ['SmcTuring.Appendix.MultiplyImage.initial_length', 'SmcTuring.Appendix.MultiplyImage.current_length', 'SmcTuring.Appendix.MultiplyImage.add_words', 'SmcTuring.Appendix.MultiplyImage.intact_current', 'SmcTuring.Appendix.MultiplyImage.fetch_current', 'SmcTuring.Appendix.MultiplyImage.initialized_packet', 'SmcTuring.Appendix.MultiplyImage.patch_owner', 'SmcTuring.Appendix.MultiplyImage.owned_field_inside', 'SmcTuring.Appendix.MultiplyImage.separated_tail', 'SmcTuring.Appendix.MultiplyImage.apart_bytes', 'SmcTuring.Appendix.MultiplyImage.image_packet', 'SmcTuring.Appendix.MultiplyImage.initialized_intact', 'SmcTuring.Appendix.MultiplyImage.frame_packet', 'SmcTuring.Appendix.MultiplyImage.store_intact', 'SmcTuring.Appendix.MultiplyImage.execute_intact']
    assert set(appendix_multiply_image_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_image_checked"] = True
    report["checked_appendix_multiply_image_declarations"] = appendix_multiply_image_names

    appendix_multiply_packing_names = ['SmcTuring.Appendix.MultiplyPacking.size_cons', 'SmcTuring.Appendix.MultiplyPacking.size_append', 'SmcTuring.Appendix.MultiplyPacking.place_append', 'SmcTuring.Appendix.MultiplyPacking.placed_lower', 'SmcTuring.Appendix.MultiplyPacking.placed_upper', 'SmcTuring.Appendix.MultiplyPacking.placed_separated', 'SmcTuring.Appendix.MultiplyPacking.initial_intact', 'SmcTuring.Appendix.MultiplyPacking.initial_fetch', 'SmcTuring.Appendix.MultiplyPacking.fields_append', 'SmcTuring.Appendix.MultiplyPacking.fields_owned', 'SmcTuring.Appendix.MultiplyPacking.same_owner_separate', 'SmcTuring.Appendix.MultiplyPacking.owned_separate', 'SmcTuring.Appendix.MultiplyPacking.field_layout', 'SmcTuring.Appendix.MultiplyPacking.placed_field_layout', 'SmcTuring.Appendix.MultiplyPacking.image_frame']
    assert set(appendix_multiply_packing_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_packing_checked"] = True
    report["checked_appendix_multiply_packing_declarations"] = appendix_multiply_packing_names

    appendix_multiply_regions_names = ['SmcTuring.Appendix.MultiplyRegions.member', 'SmcTuring.Appendix.MultiplyRegions.entry_bounds', 'SmcTuring.Appendix.MultiplyRegions.separated_append', 'SmcTuring.Appendix.MultiplyRegions.separated', 'SmcTuring.Appendix.MultiplyRegions.capacity', 'SmcTuring.Appendix.MultiplyRegions.field_layout', 'SmcTuring.Appendix.MultiplyRegions.initial_intact', 'SmcTuring.Appendix.MultiplyRegions.image_append', 'SmcTuring.Appendix.MultiplyRegions.image_frame', 'SmcTuring.Appendix.MultiplyRegions.outside_owned']
    assert set(appendix_multiply_regions_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_regions_checked"] = True
    report["checked_appendix_multiply_regions_declarations"] = appendix_multiply_regions_names

    appendix_multiply_layout_names = ['SmcTuring.Appendix.MultiplyLayout.data_initial', 'SmcTuring.Appendix.MultiplyLayout.data_initials', 'SmcTuring.Appendix.MultiplyLayout.tail_initials', 'SmcTuring.Appendix.MultiplyLayout.restore_initials', 'SmcTuring.Appendix.MultiplyLayout.pure_initials', 'SmcTuring.Appendix.MultiplyLayout.pure_size', 'SmcTuring.Appendix.MultiplyLayout.data_size', 'SmcTuring.Appendix.MultiplyLayout.tail_size', 'SmcTuring.Appendix.MultiplyLayout.restore_size', 'SmcTuring.Appendix.MultiplyLayout.data_fields', 'SmcTuring.Appendix.MultiplyLayout.tail_fields', 'SmcTuring.Appendix.MultiplyLayout.restore_fields', 'SmcTuring.Appendix.MultiplyLayout.ordered', 'SmcTuring.Appendix.MultiplyLayout.capacity', 'SmcTuring.Appendix.MultiplyLayout.separated', 'SmcTuring.Appendix.MultiplyLayout.field_layout', 'SmcTuring.Appendix.MultiplyLayout.initial_intact', 'SmcTuring.Appendix.MultiplyLayout.initial_fetch', 'SmcTuring.Appendix.MultiplyLayout.pure_fields', 'SmcTuring.Appendix.MultiplyLayout.image_fields', 'SmcTuring.Appendix.MultiplyLayout.slot_owned', 'SmcTuring.Appendix.MultiplyLayout.pointer_owned', 'SmcTuring.Appendix.MultiplyLayout.address_owned', 'SmcTuring.Appendix.MultiplyLayout.slot_fits', 'SmcTuring.Appendix.MultiplyLayout.owned_patch_intact']
    assert set(appendix_multiply_layout_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_layout_checked"] = True
    report["checked_appendix_multiply_layout_declarations"] = appendix_multiply_layout_names

    appendix_multiply_data_names = ['SmcTuring.Appendix.MultiplyData.span_cons', 'SmcTuring.Appendix.MultiplyData.instruction_length', 'SmcTuring.Appendix.MultiplyData.current_translation', 'SmcTuring.Appendix.MultiplyData.execute_pc', 'SmcTuring.Appendix.MultiplyData.constructed_trace', 'SmcTuring.Appendix.MultiplyData.image_trace', 'SmcTuring.Appendix.MultiplyData.run_pc', 'SmcTuring.Appendix.MultiplyData.block_linked', 'SmcTuring.Appendix.MultiplyData.block_dependency_owned', 'SmcTuring.Appendix.MultiplyData.block_capacity', 'SmcTuring.Appendix.MultiplyData.block_placed', 'SmcTuring.Appendix.MultiplyData.block_code_fits', 'SmcTuring.Appendix.MultiplyData.block_trace', 'SmcTuring.Appendix.MultiplyData.block_image_trace', 'SmcTuring.Appendix.MultiplyData.run_intact', 'SmcTuring.Appendix.MultiplyData.block_intact', 'SmcTuring.Appendix.MultiplyData.block_refinement']
    assert set(appendix_multiply_data_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_data_checked"] = True
    report["checked_appendix_multiply_data_declarations"] = appendix_multiply_data_names

    appendix_multiply_linear_names = ['SmcTuring.Appendix.MultiplyLinear.span_cons', 'SmcTuring.Appendix.MultiplyLinear.minimum_length', 'SmcTuring.Appendix.MultiplyLinear.execute_pc', 'SmcTuring.Appendix.MultiplyLinear.constructed_trace', 'SmcTuring.Appendix.MultiplyLinear.image_trace', 'SmcTuring.Appendix.MultiplyLinear.run_pc', 'SmcTuring.Appendix.MultiplyLinear.owned_run', 'SmcTuring.Appendix.MultiplyLinear.run_intact', 'SmcTuring.Appendix.MultiplyLinear.run_common']
    assert set(appendix_multiply_linear_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_linear_checked"] = True
    report["checked_appendix_multiply_linear_declarations"] = appendix_multiply_linear_names

    appendix_multiply_setup_names = ['SmcTuring.Appendix.MultiplySetup.call_field_position', 'SmcTuring.Appendix.MultiplySetup.tail_placed', 'SmcTuring.Appendix.MultiplySetup.continuation_placed', 'SmcTuring.Appendix.MultiplySetup.tail_fits', 'SmcTuring.Appendix.MultiplySetup.continuation_fits', 'SmcTuring.Appendix.MultiplySetup.pointer_fits', 'SmcTuring.Appendix.MultiplySetup.address_fits', 'SmcTuring.Appendix.MultiplySetup.call_fits', 'SmcTuring.Appendix.MultiplySetup.slot_alias', 'SmcTuring.Appendix.MultiplySetup.pointer_nonwrap', 'SmcTuring.Appendix.MultiplySetup.slot_apart', 'SmcTuring.Appendix.MultiplySetup.call_apart', 'SmcTuring.Appendix.MultiplySetup.metadata_outside', 'SmcTuring.Appendix.MultiplySetup.run_read_frame', 'SmcTuring.Appendix.MultiplySetup.data_read_frame', 'SmcTuring.Appendix.MultiplySetup.data_ready', 'SmcTuring.Appendix.MultiplySetup.stack_placed', 'SmcTuring.Appendix.MultiplySetup.initial_ready', 'SmcTuring.Appendix.MultiplySetup.single_owner_placed', 'SmcTuring.Appendix.MultiplySetup.initial_mov', 'SmcTuring.Appendix.MultiplySetup.initial_operands', 'SmcTuring.Appendix.MultiplySetup.call_placed', 'SmcTuring.Appendix.MultiplySetup.call_entry_initial', 'SmcTuring.Appendix.MultiplySetup.initial_call', 'SmcTuring.Appendix.MultiplySetup.fixed_call', 'SmcTuring.Appendix.MultiplySetup.word_separate', 'SmcTuring.Appendix.MultiplySetup.control_separate']
    assert set(appendix_multiply_setup_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_setup_checked"] = True
    report["checked_appendix_multiply_setup_declarations"] = appendix_multiply_setup_names

    appendix_multiply_paths_names = ['SmcTuring.Appendix.MultiplyPaths.tail_run', 'SmcTuring.Appendix.MultiplyPaths.restore_run', 'SmcTuring.Appendix.MultiplyPaths.forms_run', 'SmcTuring.Appendix.MultiplyPaths.fetched_current', 'SmcTuring.Appendix.MultiplyPaths.call_current', 'SmcTuring.Appendix.MultiplyPaths.tail_trace_intact', 'SmcTuring.Appendix.MultiplyPaths.tail_owned', 'SmcTuring.Appendix.MultiplyPaths.continuation_ownership', 'SmcTuring.Appendix.MultiplyPaths.continuation_straight', 'SmcTuring.Appendix.MultiplyPaths.continuation_span', 'SmcTuring.Appendix.MultiplyPaths.continuation_trace', 'SmcTuring.Appendix.MultiplyPaths.continuation_intact', 'SmcTuring.Appendix.MultiplyPaths.continued_effect', 'SmcTuring.Appendix.MultiplyPaths.continued_ready', 'SmcTuring.Appendix.MultiplyPaths.continued_intact', 'SmcTuring.Appendix.MultiplyPaths.tail_target_pc', 'SmcTuring.Appendix.MultiplyPaths.continued_trace', 'SmcTuring.Appendix.MultiplyPaths.continued_owned']
    assert set(appendix_multiply_paths_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_paths_checked"] = True
    report["checked_appendix_multiply_paths_declarations"] = appendix_multiply_paths_names

    appendix_multiply_byte_blocks_names = ['SmcTuring.Appendix.MultiplyByteBlocks.view_agreement', 'SmcTuring.Appendix.MultiplyByteBlocks.forms_run', 'SmcTuring.Appendix.MultiplyByteBlocks.data_end_pc', 'SmcTuring.Appendix.MultiplyByteBlocks.guard_displacement', 'SmcTuring.Appendix.MultiplyByteBlocks.target', 'SmcTuring.Appendix.MultiplyByteBlocks.run_effect', 'SmcTuring.Appendix.MultiplyByteBlocks.trace', 'SmcTuring.Appendix.MultiplyByteBlocks.image_trace', 'SmcTuring.Appendix.MultiplyByteBlocks.run_intact', 'SmcTuring.Appendix.MultiplyByteBlocks.run_ready', 'SmcTuring.Appendix.MultiplyByteBlocks.owned', 'SmcTuring.Appendix.MultiplyByteBlocks.refinement', 'SmcTuring.Appendix.MultiplyByteBlocks.run_pc', 'SmcTuring.Appendix.MultiplyByteBlocks.field', 'SmcTuring.Appendix.MultiplyByteBlocks.stack']
    assert set(appendix_multiply_byte_blocks_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_blocks_checked"] = True
    report["checked_appendix_multiply_byte_blocks_declarations"] = appendix_multiply_byte_blocks_names

    appendix_multiply_byte_simulation_names = ['SmcTuring.Appendix.MultiplyByteSimulation.view_agreement', 'SmcTuring.Appendix.MultiplyByteSimulation.slot_word', 'SmcTuring.Appendix.MultiplyByteSimulation.source_ready', 'SmcTuring.Appendix.MultiplyByteSimulation.block_start', 'SmcTuring.Appendix.MultiplyByteSimulation.guard_ready', 'SmcTuring.Appendix.MultiplyByteSimulation.source_data_effect', 'SmcTuring.Appendix.MultiplyByteSimulation.source_stack_effect', 'SmcTuring.Appendix.MultiplyByteSimulation.block', 'SmcTuring.Appendix.MultiplyByteSimulation.advance']
    assert set(appendix_multiply_byte_simulation_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_simulation_checked"] = True
    report["checked_appendix_multiply_byte_simulation_declarations"] = appendix_multiply_byte_simulation_names

    appendix_multiply_byte_loop_names = ['SmcTuring.Appendix.MultiplyByteLoop.entry_location', 'SmcTuring.Appendix.MultiplyByteLoop.body_boundary', 'SmcTuring.Appendix.MultiplyByteLoop.exit_simulate', 'SmcTuring.Appendix.MultiplyByteLoop.simulate']
    assert set(appendix_multiply_byte_loop_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_loop_checked"] = True
    report["checked_appendix_multiply_byte_loop_declarations"] = appendix_multiply_byte_loop_names

    appendix_multiply_byte_correct_names = ['SmcTuring.Appendix.MultiplyByteCorrect.initial_context', 'SmcTuring.Appendix.MultiplyByteCorrect.multiply_simulate', 'SmcTuring.Appendix.MultiplyByteCorrect.execution', 'SmcTuring.Appendix.MultiplyByteCorrect.owned_run_frame', 'SmcTuring.Appendix.MultiplyByteCorrect.trace_frame', 'SmcTuring.Appendix.MultiplyByteCorrect.field_cases', 'SmcTuring.Appendix.MultiplyByteCorrect.correct']
    assert set(appendix_multiply_byte_correct_names) <= {item["name"] for item in declarations}
    report["appendix_multiply_byte_correct_checked"] = True
    report["checked_appendix_multiply_byte_correct_declarations"] = appendix_multiply_byte_correct_names

    appendix_constant_names = ['SmcTuring.Appendix.ConstantAlgebra.zeros_lt', 'SmcTuring.Appendix.ConstantAlgebra.lower_bits_zero', 'SmcTuring.Appendix.ConstantAlgebra.quotient_odd', 'SmcTuring.Appendix.ConstantAlgebra.rest_toNat', 'SmcTuring.Appendix.ConstantAlgebra.decomposition_nat', 'SmcTuring.Appendix.ConstantAlgebra.decomposition', 'SmcTuring.Appendix.ConstantAlgebra.shifted', 'SmcTuring.Appendix.ConstantAlgebra.scale_successor', 'SmcTuring.Appendix.ConstantAlgebra.rest_bound', 'SmcTuring.Appendix.ConstantAlgebra.gap_invariant', 'SmcTuring.Appendix.ConstantAlgebra.tail_correct', 'SmcTuring.Appendix.ConstantAlgebra.first_invariant', 'SmcTuring.Appendix.ConstantAlgebra.correct', 'SmcTuring.Appendix.ConstantAlgebra.gap_count_lt', 'SmcTuring.Appendix.ConstantAlgebra.rest_decreases', 'SmcTuring.Appendix.ConstantAlgebra.top_bit_consumed', 'SmcTuring.Appendix.ConstantAlgebra.zero_correct', 'SmcTuring.Appendix.ConstantAlgebra.signed_low_product', 'SmcTuring.Appendix.ConstantWords.run_append', 'SmcTuring.Appendix.ConstantWords.execute_frame', 'SmcTuring.Appendix.ConstantWords.shift_data', 'SmcTuring.Appendix.ConstantWords.shift_frame', 'SmcTuring.Appendix.ConstantWords.shift_accumulator', 'SmcTuring.Appendix.ConstantWords.copy_effect', 'SmcTuring.Appendix.ConstantWords.accumulate_effect', 'SmcTuring.Appendix.ConstantWords.tail_data', 'SmcTuring.Appendix.ConstantWords.correct', 'SmcTuring.Appendix.ConstantWords.shift_legal', 'SmcTuring.Appendix.ConstantWords.tail_legal', 'SmcTuring.Appendix.ConstantWords.program_legal', 'SmcTuring.Appendix.ConstantWords.tail_owned', 'SmcTuring.Appendix.ConstantWords.program_owned', 'SmcTuring.Appendix.ConstantWords.run_frame', 'SmcTuring.Appendix.ConstantWords.frame', 'SmcTuring.Appendix.ConstantWords.tail_accumulator', 'SmcTuring.Appendix.ConstantWords.accumulator', 'SmcTuring.Appendix.ConstantWords.pure_of_owned_legal', 'SmcTuring.Appendix.ConstantWords.pure', 'SmcTuring.Appendix.ConstantWords.tail_length', 'SmcTuring.Appendix.ConstantWords.program_length', 'SmcTuring.Appendix.ConstantWords.contract']
    assert set(appendix_constant_names) <= {item["name"] for item in declarations}
    report["appendix_constant_word_checked"] = True
    report["checked_appendix_constant_word_declarations"] = appendix_constant_names

    appendix_constant_byte_names = ['SmcTuring.Appendix.ConstantByteCode.count_byte', 'SmcTuring.Appendix.ConstantByteCode.count_bounds', 'SmcTuring.Appendix.ConstantByteCode.shift_payload', 'SmcTuring.Appendix.ConstantByteCode.common_decode', 'SmcTuring.Appendix.ConstantByteCode.form_roundtrip', 'SmcTuring.Appendix.ConstantByteCode.encode_injective', 'SmcTuring.Appendix.ConstantByteCode.encode_length', 'SmcTuring.Appendix.ConstantByteCode.length_bounds', 'SmcTuring.Appendix.ConstantByteCode.common_length', 'SmcTuring.Appendix.ConstantByteCode.encoded_length', 'SmcTuring.Appendix.ConstantByteCode.length_take_two', 'SmcTuring.Appendix.ConstantByteCode.fetch_current_encoding', 'SmcTuring.Appendix.ConstantByteCode.fetch_written_encoding', 'SmcTuring.Appendix.ConstantByteCode.fetch_patched_current_add', 'SmcTuring.Appendix.ConstantByteExecution.execute_effect', 'SmcTuring.Appendix.ConstantByteExecution.execute_memory', 'SmcTuring.Appendix.ConstantByteExecution.execute_accumulator', 'SmcTuring.Appendix.ConstantByteExecution.execute_stack', 'SmcTuring.Appendix.ConstantByteExecution.execute_carry', 'SmcTuring.Appendix.ConstantByteExecution.execute_pc', 'SmcTuring.Appendix.ConstantByteExecution.written_word', 'SmcTuring.Appendix.ConstantByteExecution.execute_frame', 'SmcTuring.Appendix.ConstantByteExecution.load_frame', 'SmcTuring.Appendix.ConstantByteExecution.footprint_length', 'SmcTuring.Appendix.ConstantByteExecution.footprint_nonempty', 'SmcTuring.Appendix.ConstantByteExecution.common_execution', 'SmcTuring.Appendix.ConstantByteExecution.shift_carry', 'SmcTuring.Appendix.ConstantByteExecution.step_current_encoding', 'SmcTuring.Appendix.ConstantByteExecution.step_patched_add', 'SmcTuring.Appendix.ConstantByteExecution.trace_run', 'SmcTuring.Appendix.ConstantByteExecution.run_append', 'SmcTuring.Appendix.ConstantByteExecution.trace_append', 'SmcTuring.Appendix.ConstantByteExecution.owned_append', 'SmcTuring.Appendix.ConstantRefinement.count_value', 'SmcTuring.Appendix.ConstantRefinement.destination_dependency', 'SmcTuring.Appendix.ConstantRefinement.translate_destination', 'SmcTuring.Appendix.ConstantRefinement.translate_value', 'SmcTuring.Appendix.ConstantRefinement.translate_accumulator', 'SmcTuring.Appendix.ConstantRefinement.translate_carry', 'SmcTuring.Appendix.ConstantRefinement.translate_stack', 'SmcTuring.Appendix.ConstantRefinement.translate_length', 'SmcTuring.Appendix.ConstantRefinement.execute_pc', 'SmcTuring.Appendix.ConstantRefinement.execute_read_destination', 'SmcTuring.Appendix.ConstantRefinement.execute_read_frame', 'SmcTuring.Appendix.ConstantRefinement.simulate', 'SmcTuring.Appendix.ConstantRefinement.forms_length', 'SmcTuring.Appendix.ConstantRefinement.forms_run', 'SmcTuring.Appendix.ConstantRefinement.simulate_run', 'SmcTuring.Appendix.ConstantRefinement.run_stack', 'SmcTuring.Appendix.ConstantRefinement.run_frame', 'SmcTuring.Appendix.ConstantRefinement.owned_run', 'SmcTuring.Appendix.ConstantImage.initial_length', 'SmcTuring.Appendix.ConstantImage.current_length', 'SmcTuring.Appendix.ConstantImage.intact_current', 'SmcTuring.Appendix.ConstantImage.fetch_current', 'SmcTuring.Appendix.ConstantImage.initialized_packet', 'SmcTuring.Appendix.ConstantImage.patch_owner', 'SmcTuring.Appendix.ConstantImage.owned_field_inside', 'SmcTuring.Appendix.ConstantImage.separated_tail', 'SmcTuring.Appendix.ConstantImage.apart_bytes', 'SmcTuring.Appendix.ConstantImage.image_packet', 'SmcTuring.Appendix.ConstantImage.initialized_intact', 'SmcTuring.Appendix.ConstantImage.frame_packet', 'SmcTuring.Appendix.ConstantImage.store_intact', 'SmcTuring.Appendix.ConstantImage.execute_intact', 'SmcTuring.Appendix.ConstantPacking.size_cons', 'SmcTuring.Appendix.ConstantPacking.size_append', 'SmcTuring.Appendix.ConstantPacking.place_append', 'SmcTuring.Appendix.ConstantPacking.placed_lower', 'SmcTuring.Appendix.ConstantPacking.placed_upper', 'SmcTuring.Appendix.ConstantPacking.placed_separated', 'SmcTuring.Appendix.ConstantPacking.initial_intact', 'SmcTuring.Appendix.ConstantPacking.initial_fetch', 'SmcTuring.Appendix.ConstantPacking.fields_append', 'SmcTuring.Appendix.ConstantPacking.fields_owned', 'SmcTuring.Appendix.ConstantPacking.same_owner_separate', 'SmcTuring.Appendix.ConstantPacking.owned_separate', 'SmcTuring.Appendix.ConstantPacking.field_layout', 'SmcTuring.Appendix.ConstantPacking.placed_field_layout', 'SmcTuring.Appendix.ConstantPacking.image_frame', 'SmcTuring.Appendix.ConstantData.span_cons', 'SmcTuring.Appendix.ConstantData.instruction_length', 'SmcTuring.Appendix.ConstantData.current_translation', 'SmcTuring.Appendix.ConstantData.execute_pc', 'SmcTuring.Appendix.ConstantData.constructed_trace', 'SmcTuring.Appendix.ConstantData.image_trace', 'SmcTuring.Appendix.ConstantData.run_pc', 'SmcTuring.Appendix.ConstantData.run_intact', 'SmcTuring.Appendix.ConstantSimulation.shift_uses', 'SmcTuring.Appendix.ConstantSimulation.copy_uses', 'SmcTuring.Appendix.ConstantSimulation.accumulate_uses', 'SmcTuring.Appendix.ConstantSimulation.tail_uses', 'SmcTuring.Appendix.ConstantSimulation.program_uses', 'SmcTuring.Appendix.ConstantSimulation.view_agreement', 'SmcTuring.Appendix.ConstantSimulation.compiled_agreement', 'SmcTuring.Appendix.ConstantSimulation.carry', 'SmcTuring.Appendix.ConstantSimulation.effect', 'SmcTuring.Appendix.ConstantSimulation.two_field_layout', 'SmcTuring.Appendix.ConstantSimulation.original_image_correct']
    assert set(appendix_constant_byte_names) <= {item["name"] for item in declarations}
    report["appendix_constant_byte_checked"] = True
    report["checked_appendix_constant_byte_declarations"] = appendix_constant_byte_names

    appendix_constant_geometry_names = ['SmcTuring.Appendix.ConstantShape.span_append', 'SmcTuring.Appendix.ConstantShape.shift_span', 'SmcTuring.Appendix.ConstantShape.copy_span', 'SmcTuring.Appendix.ConstantShape.accumulate_span', 'SmcTuring.Appendix.ConstantShape.tail_span_independent', 'SmcTuring.Appendix.ConstantShape.program_span_independent', 'SmcTuring.Appendix.ConstantShape.plain_append', 'SmcTuring.Appendix.ConstantShape.shift_plain', 'SmcTuring.Appendix.ConstantShape.copy_plain', 'SmcTuring.Appendix.ConstantShape.accumulate_plain', 'SmcTuring.Appendix.ConstantShape.plain_linked', 'SmcTuring.Appendix.ConstantShape.linked_append', 'SmcTuring.Appendix.ConstantShape.tail_shape', 'SmcTuring.Appendix.ConstantShape.program_shape', 'SmcTuring.Appendix.ConstantShape.inactive_plain', 'SmcTuring.Appendix.ConstantShape.active_span', 'SmcTuring.Appendix.ConstantShape.active_linked', 'SmcTuring.Appendix.ConstantShape.active_owned', 'SmcTuring.Appendix.ConstantRegions.member', 'SmcTuring.Appendix.ConstantRegions.entry_bounds', 'SmcTuring.Appendix.ConstantRegions.separated_append', 'SmcTuring.Appendix.ConstantRegions.separated', 'SmcTuring.Appendix.ConstantRegions.capacity', 'SmcTuring.Appendix.ConstantRegions.field_layout', 'SmcTuring.Appendix.ConstantRegions.initial_intact', 'SmcTuring.Appendix.ConstantRegions.image_append', 'SmcTuring.Appendix.ConstantRegions.image_frame', 'SmcTuring.Appendix.ConstantRegions.outside_owned', 'SmcTuring.Appendix.ConstantGeometry.ops_span', 'SmcTuring.Appendix.ConstantGeometry.storage_size', 'SmcTuring.Appendix.ConstantGeometry.linked', 'SmcTuring.Appendix.ConstantGeometry.placed', 'SmcTuring.Appendix.ConstantGeometry.separated', 'SmcTuring.Appendix.ConstantGeometry.capacity', 'SmcTuring.Appendix.ConstantGeometry.data_member', 'SmcTuring.Appendix.ConstantGeometry.data_owned', 'SmcTuring.Appendix.ConstantGeometry.scratch_owned', 'SmcTuring.Appendix.ConstantGeometry.distinct', 'SmcTuring.Appendix.ConstantGeometry.code_fits', 'SmcTuring.Appendix.ConstantGeometry.two_field_layout', 'SmcTuring.Appendix.ConstantCorrect.data_initial', 'SmcTuring.Appendix.ConstantCorrect.correct', 'SmcTuring.Appendix.ConstantCorrect.reusable_trace', 'SmcTuring.Appendix.ConstantCorrect.reusable_correct']
    assert set(appendix_constant_geometry_names) <= {item["name"] for item in declarations}
    report["appendix_constant_geometry_checked"] = True
    report["checked_appendix_constant_geometry_declarations"] = appendix_constant_geometry_names

    appendix_zero_names = ['SmcTuring.Appendix.ZeroImage.packet_length', 'SmcTuring.Appendix.ZeroImage.field_owned', 'SmcTuring.Appendix.ZeroImage.separated', 'SmcTuring.Appendix.ZeroImage.initial_intact', 'SmcTuring.Appendix.ZeroImage.current_form', 'SmcTuring.Appendix.ZeroImage.current_value', 'SmcTuring.Appendix.ZeroImage.fetched', 'SmcTuring.Appendix.ZeroImage.step_correct', 'SmcTuring.Appendix.ZeroImage.effect', 'SmcTuring.Appendix.ZeroImage.written_zero', 'SmcTuring.Appendix.ZeroImage.intact_after', 'SmcTuring.Appendix.ZeroImage.frame', 'SmcTuring.Appendix.ZeroImage.trace', 'SmcTuring.Appendix.ZeroImage.owned_run', 'SmcTuring.Appendix.ZeroImage.correct', 'SmcTuring.Appendix.ZeroImage.original_image_correct', 'SmcTuring.Appendix.ZeroImage.reentry_intact', 'SmcTuring.Appendix.ZeroImage.reentry_trace']
    assert set(appendix_zero_names) <= {item["name"] for item in declarations}
    report["appendix_zero_checked"] = True
    report["checked_appendix_zero_declarations"] = appendix_zero_names



    native_conversion_names = ['SmcTuring.Native.ConversionLayout.lengths', 'SmcTuring.Native.ConversionLayout.span_size', 'SmcTuring.Native.ConversionLayout.placed_entries', 'SmcTuring.Native.ConversionLayout.endpoint', 'SmcTuring.Native.ConversionLayout.separated', 'SmcTuring.Native.ConversionLayout.source_toNat', 'SmcTuring.Native.ConversionLayout.destination_toNat', 'SmcTuring.Native.ConversionLayout.outside', 'SmcTuring.Native.ConversionLayout.first_hits', 'SmcTuring.Native.ConversionLayout.second_hits', 'SmcTuring.Native.ConversionLayout.third_hits', 'SmcTuring.Native.ConversionLayout.first_next', 'SmcTuring.Native.ConversionLayout.second_next', 'SmcTuring.Native.ConversionLayout.third_next', 'SmcTuring.Native.ConversionEffects.source_outside', 'SmcTuring.Native.ConversionEffects.destination_outside', 'SmcTuring.Native.ConversionEffects.first_effect', 'SmcTuring.Native.ConversionEffects.second_effect', 'SmcTuring.Native.ConversionEffects.third_effect', 'SmcTuring.Native.ConversionEffects.swapped_pc', 'SmcTuring.Native.ConversionEffects.stored_effect', 'SmcTuring.Native.ConversionEffects.stored_pc', 'SmcTuring.Native.ConversionEffects.original_source_read', 'SmcTuring.Native.ConversionEffects.source_read_after_stored', 'SmcTuring.Native.ConversionEffects.restored_memory', 'SmcTuring.Native.ConversionEffects.effect', 'SmcTuring.Native.ConversionEffects.destination_value', 'SmcTuring.Native.ConversionEffects.source_value', 'SmcTuring.Native.ConversionEffects.frame', 'SmcTuring.Native.ConversionImage.initial_intact', 'SmcTuring.Native.ConversionImage.source_external', 'SmcTuring.Native.ConversionImage.destination_external', 'SmcTuring.Native.ConversionImage.swapped_intact', 'SmcTuring.Native.ConversionImage.stored_intact', 'SmcTuring.Native.ConversionImage.finish_intact', 'SmcTuring.Native.ConversionImage.fetched', 'SmcTuring.Native.ConversionImage.trace', 'SmcTuring.Native.ConversionImage.correct', 'SmcTuring.Native.ConversionImage.original_image_correct', 'SmcTuring.Native.ConversionImage.reentry_trace', 'SmcTuring.Native.ConversionImage.reentry_effect', 'SmcTuring.Native.ConversionOperands.owner_prefix_outside', 'SmcTuring.Native.ConversionOperands.destination_prefix', 'SmcTuring.Native.ConversionOperands.destination_fetch', 'SmcTuring.Native.ConversionOperands.source_prefix', 'SmcTuring.Native.ConversionOperands.source_fetch', 'SmcTuring.Native.ConversionOwnership.first_address', 'SmcTuring.Native.ConversionOwnership.second_address', 'SmcTuring.Native.ConversionOwnership.third_address', 'SmcTuring.Native.ConversionOwnership.supported_run', 'SmcTuring.Native.ConversionOwnership.code_owned_run', 'SmcTuring.Native.ConversionOwnership.whole_intact', 'SmcTuring.Native.ConversionOwnership.original_image_correct']
    assert set(native_conversion_names) <= {item["name"] for item in declarations}
    report["native_conversion_checked"] = True
    report["checked_native_conversion_declarations"] = native_conversion_names

    native_string_copy_names = ['SmcTuring.Native.StringCopy.adjacent_put', 'SmcTuring.Native.StringCopy.empty_put', 'SmcTuring.Native.StringCopy.apart_tail', 'SmcTuring.Native.StringCopy.source_outside', 'SmcTuring.Native.StringCopy.tail_read', 'SmcTuring.Native.StringCopy.effect', 'SmcTuring.Native.StringCopy.copied', 'SmcTuring.Native.StringCopy.source_preserved', 'SmcTuring.Native.StringCopy.frame', 'SmcTuring.Native.StringCopy.run_append', 'SmcTuring.Native.StringPlan.sum_replicate', 'SmcTuring.Native.StringPlan.total', 'SmcTuring.Native.StringPlan.remainder_two', 'SmcTuring.Native.StringPlan.remainder_four', 'SmcTuring.Native.StringPlan.remainder_one', 'SmcTuring.Native.StringPlan.two_bit_count', 'SmcTuring.Native.StringPlan.four_bit_count', 'SmcTuring.Native.StringPlan.one_bit_count', 'SmcTuring.Native.StringPlan.literal_widths', 'SmcTuring.Native.StringPlan.legal', 'SmcTuring.Native.StringPlan.positive', 'SmcTuring.Native.StringPlan.opcode_nonempty', 'SmcTuring.Native.StringPlan.opcode_length', 'SmcTuring.Native.StringPlan.correct', 'SmcTuring.Native.StringPlan.copied', 'SmcTuring.Native.StringPlan.source_preserved', 'SmcTuring.Native.StringPlan.frame', 'SmcTuring.Native.StringCursor.exchange_twice', 'SmcTuring.Native.StringCursor.effect', 'SmcTuring.Native.StringCursor.advanced_pointer', 'SmcTuring.Native.StringCursor.restored_index', 'SmcTuring.Native.StringCursor.restored_field', 'SmcTuring.Native.StringCursor.encoded_sum', 'SmcTuring.Native.StringCursor.advanced_toNat', 'SmcTuring.Native.StringCursor.no_borrow', 'SmcTuring.Native.StringCursor.pair_correct', 'SmcTuring.Native.StringFields.prepared_source', 'SmcTuring.Native.StringFields.copied_effect', 'SmcTuring.Native.StringFields.cursor_outside', 'SmcTuring.Native.StringFields.copy_word_commute', 'SmcTuring.Native.StringFields.restored_fields', 'SmcTuring.Native.StringFields.effect', 'SmcTuring.Native.StringFields.destination_value', 'SmcTuring.Native.StringFields.frame', 'SmcTuring.Native.StringCodec.initial_length', 'SmcTuring.Native.StringCodec.exchange_length', 'SmcTuring.Native.StringCodec.sub_length', 'SmcTuring.Native.StringCodec.field_end', 'SmcTuring.Native.StringCodec.destination_field_end', 'SmcTuring.Native.StringCodec.body_coordinate', 'SmcTuring.Native.StringCodec.whole_length']
    assert set(native_string_copy_names) <= {item["name"] for item in declarations}
    report["native_string_copy_checked"] = True
    report["checked_native_string_copy_declarations"] = native_string_copy_names

    native_string_execution_names = ['SmcTuring.Native.StringForm.native_extra_none', 'SmcTuring.Native.StringForm.native_decode', 'SmcTuring.Native.StringForm.form_roundtrip', 'SmcTuring.Native.StringForm.native_extra_length_none', 'SmcTuring.Native.StringForm.encoded_length', 'SmcTuring.Native.StringForm.length_bound', 'SmcTuring.Native.StringForm.length_take_three', 'SmcTuring.Native.StringForm.fetch_current_encoding', 'SmcTuring.Native.StringExecution.native_effect', 'SmcTuring.Native.StringExecution.native_indices', 'SmcTuring.Native.StringExecution.direction_preserved', 'SmcTuring.Native.StringExecution.run_direction', 'SmcTuring.Native.StringExecution.move_effect', 'SmcTuring.Native.StringExecution.move_frame', 'SmcTuring.Native.StringExecution.move_accumulator', 'SmcTuring.Native.StringExecution.move_stack', 'SmcTuring.Native.StringExecution.move_carry', 'SmcTuring.Native.StringExecution.exchange_source', 'SmcTuring.Native.StringExecution.exchange_destination', 'SmcTuring.Native.StringExecution.trace_run', 'SmcTuring.Native.StringExecution.run_append', 'SmcTuring.Native.StringExecution.trace_append', 'SmcTuring.Native.StringExecution.step_current_encoding', 'SmcTuring.Native.StringMoves.code_cons', 'SmcTuring.Native.StringMoves.span_cons', 'SmcTuring.Native.StringMoves.index_advance', 'SmcTuring.Native.StringMoves.move_view', 'SmcTuring.Native.StringMoves.run_view', 'SmcTuring.Native.StringMoves.run_pc', 'SmcTuring.Native.StringMoves.run_source', 'SmcTuring.Native.StringMoves.run_destination', 'SmcTuring.Native.StringMoves.run_accumulator', 'SmcTuring.Native.StringMoves.run_stack', 'SmcTuring.Native.StringMoves.run_carry', 'SmcTuring.Native.StringMoves.effect', 'SmcTuring.Native.StringMoves.copied', 'SmcTuring.Native.StringMoves.frame', 'SmcTuring.Native.StringMoveTrace.current_head', 'SmcTuring.Native.StringMoveTrace.current_tail', 'SmcTuring.Native.StringMoveTrace.tail_separate', 'SmcTuring.Native.StringMoveTrace.next_location', 'SmcTuring.Native.StringMoveTrace.constructed_trace', 'SmcTuring.Native.StringMoveTrace.image_trace', 'SmcTuring.Native.StringMoveTrace.correct', 'SmcTuring.Native.StringMoveTrace.code_preserved', 'SmcTuring.Native.StringTemplate.copied_window', 'SmcTuring.Native.StringTemplate.copied_fetch', 'SmcTuring.Native.StringTemplate.delta_internal', 'SmcTuring.Native.StringTemplate.relative_internal', 'SmcTuring.Native.StringTemplate.signed_internal', 'SmcTuring.Native.StringTemplate.rip_internal', 'SmcTuring.Native.StringTemplate.rip_target', 'SmcTuring.Native.StringTemplate.absolute_external', 'SmcTuring.Native.StringTemplate.absolute_target']
    assert set(native_string_execution_names) <= {item["name"] for item in declarations}
    report["native_string_execution_checked"] = True
    report["checked_native_string_execution_declarations"] = native_string_execution_names

    native_string_stage_names = ['SmcTuring.Native.StringOperands.exchange_encoding', 'SmcTuring.Native.StringOperands.exchange_length', 'SmcTuring.Native.StringOperands.sign_extend_small', 'SmcTuring.Native.StringOperands.sign_extend_full', 'SmcTuring.Native.StringOperands.subtract_encoding', 'SmcTuring.Native.StringOperands.subtract_length', 'SmcTuring.Native.StringOperands.exchange_hits', 'SmcTuring.Native.StringOperands.subtract_next', 'SmcTuring.Native.StringOperands.subtract_effect', 'SmcTuring.Native.StringOperands.source_effect', 'SmcTuring.Native.StringOperands.destination_effect', 'SmcTuring.Native.StringWindow.bytes_at_slice', 'SmcTuring.Native.StringWindow.packet_window', 'SmcTuring.Native.StringWindow.initial_word', 'SmcTuring.Native.StringWindow.load_frame', 'SmcTuring.Native.StringInit.first_displacement', 'SmcTuring.Native.StringInit.second_displacement', 'SmcTuring.Native.StringInit.leading_length', 'SmcTuring.Native.StringInit.initial_shape', 'SmcTuring.Native.StringInit.forms_encoding', 'SmcTuring.Native.StringInit.initialized_pointer', 'SmcTuring.Native.StringInit.native_run', 'SmcTuring.Native.StringInit.effect', 'SmcTuring.Native.StringRestore.forms_encoding', 'SmcTuring.Native.StringRestore.no_borrow', 'SmcTuring.Native.StringRestore.loaded_exchange', 'SmcTuring.Native.StringRestore.source_effect', 'SmcTuring.Native.StringRestore.destination_effect', 'SmcTuring.Native.StringRestore.trace', 'SmcTuring.Native.StringInitTrace.trace', 'SmcTuring.Native.StringSetup.cursor_range', 'SmcTuring.Native.StringSetup.source_field_fits', 'SmcTuring.Native.StringSetup.destination_field_fits', 'SmcTuring.Native.StringSetup.initializer_fits', 'SmcTuring.Native.StringSetup.source_effect', 'SmcTuring.Native.StringSetup.destination_window', 'SmcTuring.Native.StringSetup.effect', 'SmcTuring.Native.StringSetupTrace.forms_encoding', 'SmcTuring.Native.StringSetupTrace.source_field_frame', 'SmcTuring.Native.StringSetupTrace.source_trace', 'SmcTuring.Native.StringSetupTrace.trace', 'SmcTuring.Native.StringSetupTrace.initialized_trace', 'SmcTuring.Native.StringProgram.body_encoding', 'SmcTuring.Native.StringProgram.prefix_extent', 'SmcTuring.Native.StringProgram.encoding', 'SmcTuring.Native.StringProgram.code_extent', 'SmcTuring.Native.StringProgram.instruction_count', 'SmcTuring.Native.StringProgram.setup_legal', 'SmcTuring.Native.StringProgram.restore_legal', 'SmcTuring.Native.StringProgram.legal']
    assert set(native_string_stage_names) <= {item["name"] for item in declarations}
    report["native_string_stages_checked"] = True
    report["checked_native_string_stage_declarations"] = native_string_stage_names

    native_string_macro_names = ['SmcTuring.Native.StringMacroLayout.split_bytes', 'SmcTuring.Native.StringMacroLayout.coordinates', 'SmcTuring.Native.StringMacroLayout.field_coordinates', 'SmcTuring.Native.StringMacroLayout.repeat_length', 'SmcTuring.Native.StringMacroLayout.body_bound', 'SmcTuring.Native.StringMacroLayout.span_bound', 'SmcTuring.Native.StringMacroLayout.internal_range', 'SmcTuring.Native.StringMacroLayout.tail_ranges', 'SmcTuring.Native.StringMacroLayout.source_capacity', 'SmcTuring.Native.StringMacroLayout.destination_capacity', 'SmcTuring.Native.StringMacroLayout.prefix_capacity', 'SmcTuring.Native.StringMacroLayout.fields_separate', 'SmcTuring.Native.StringMacroLayout.source_cursor_frame', 'SmcTuring.Native.StringMacroLayout.destination_cursor_frame', 'SmcTuring.Native.StringMacroLayout.copy_code_frame', 'SmcTuring.Native.StringMacroImage.windows', 'SmcTuring.Native.StringMacroImage.initializer_windows', 'SmcTuring.Native.StringMacroImage.initialized_pointers', 'SmcTuring.Native.StringMacroImage.initial_words', 'SmcTuring.Native.StringMacroImage.destination_word_outside', 'SmcTuring.Native.StringMacroImage.prefix_effect', 'SmcTuring.Native.StringMacroImage.prefix_trace', 'SmcTuring.Native.StringMacroImage.prepared_window', 'SmcTuring.Native.StringMacroEffects.state_eq', 'SmcTuring.Native.StringMacroEffects.setup_effect', 'SmcTuring.Native.StringMacroEffects.copied_effect', 'SmcTuring.Native.StringMacroEffects.copied_source_load', 'SmcTuring.Native.StringMacroEffects.copied_destination_load', 'SmcTuring.Native.StringMacroEffects.source_effect', 'SmcTuring.Native.StringMacroEffects.source_destination_load', 'SmcTuring.Native.StringMacroEffects.finish_effect', 'SmcTuring.Native.StringMacroEffects.program_run', 'SmcTuring.Native.StringMacroTrace.setup_trace', 'SmcTuring.Native.StringMacroTrace.body_trace', 'SmcTuring.Native.StringMacroTrace.copied_window', 'SmcTuring.Native.StringMacroTrace.source_trace', 'SmcTuring.Native.StringMacroTrace.destination_window', 'SmcTuring.Native.StringMacroTrace.destination_trace', 'SmcTuring.Native.StringMacroTrace.trace', 'SmcTuring.Native.StringMacroTrace.correct', 'SmcTuring.Native.StringMacroTrace.code_preserved', 'SmcTuring.Native.StringMacroTrace.reusable', 'SmcTuring.Native.StringMacroTrace.run_correct', 'SmcTuring.Native.StringMacroTrace.frame', 'SmcTuring.Native.StringMacroTrace.source_preserved', 'SmcTuring.Native.StringMacroTrace.reentry_trace']
    assert set(native_string_macro_names) <= {item["name"] for item in declarations}
    report["native_string_macro_checked"] = True
    report["checked_native_string_macro_declarations"] = native_string_macro_names

    native_template_copy_names = ['SmcTuring.Native.TemplateRelocation.bound_length', 'SmcTuring.Native.TemplateRelocation.encoded_length', 'SmcTuring.Native.TemplateRelocation.length_positive', 'SmcTuring.Native.TemplateRelocation.length_bound', 'SmcTuring.Native.TemplateRelocation.bytes_cons', 'SmcTuring.Native.TemplateRelocation.bytes_length', 'SmcTuring.Native.TemplateRelocation.instruction_count', 'SmcTuring.Native.TemplateRelocation.places_lower', 'SmcTuring.Native.TemplateRelocation.places_upper', 'SmcTuring.Native.TemplateRelocation.bound_member', 'SmcTuring.Native.TemplateRelocation.whole_packet', 'SmcTuring.Native.TemplateRelocation.whole_fetch', 'SmcTuring.Native.TemplateRelocation.moffs_address', 'SmcTuring.Native.TemplateRelocation.moffs_field', 'SmcTuring.Native.TemplateRelocation.memory_field', 'SmcTuring.Native.TemplateRelocation.memory_target', 'SmcTuring.Native.TemplateRelocation.call_target', 'SmcTuring.Native.TemplateRelocation.internal_rip', 'SmcTuring.Native.TemplateRelocation.internal_call', 'SmcTuring.Native.TemplateRelocation.external_moffs', 'SmcTuring.Native.TemplateRelocation.external_absolute', 'SmcTuring.Native.TemplateRelocation.moffs_position', 'SmcTuring.Native.TemplateRelocation.memory_position', 'SmcTuring.Native.TemplateRelocation.call_position', 'SmcTuring.Native.TemplateCopy.complete_image', 'SmcTuring.Native.TemplateCopy.packet', 'SmcTuring.Native.TemplateCopy.fetch', 'SmcTuring.Native.TemplateCopy.packet_capacity', 'SmcTuring.Native.TemplateCopy.moffs_payload', 'SmcTuring.Native.TemplateCopy.memory_target', 'SmcTuring.Native.TemplateCopy.call_target', 'SmcTuring.Native.TemplateCopy.correct', 'SmcTuring.Native.TemplateCopy.initialized_blueprint', 'SmcTuring.Native.TemplateCopy.initialized_macro', 'SmcTuring.Native.TemplateCopy.ready_initialized', 'SmcTuring.Native.TemplateCopy.ready_initial', 'SmcTuring.Native.TemplateCopy.original_image_correct', 'SmcTuring.Native.TemplateCopy.internal_target_capacity', 'SmcTuring.Native.TemplateCopy.moffs_position', 'SmcTuring.Native.TemplateRelocation.observed_target', 'SmcTuring.Native.TemplateCopy.original_addresses_correct']
    assert set(native_template_copy_names) <= {item["name"] for item in declarations}
    report["native_template_copy_checked"] = True
    report["checked_native_template_copy_declarations"] = native_template_copy_names

    division_foundation_names = ['SmcTuring.Appendix.DivisionAlgebra.step_processed', 'SmcTuring.Appendix.DivisionAlgebra.step_valid', 'SmcTuring.Appendix.DivisionAlgebra.scan_valid', 'SmcTuring.Appendix.DivisionAlgebra.scan_processed', 'SmcTuring.Appendix.DivisionAlgebra.scan_correct', 'SmcTuring.Appendix.DivisionAlgebra.remainder_le_processed', 'SmcTuring.Appendix.DivisionAlgebra.trial_fits', 'SmcTuring.Appendix.DivisionAlgebra.full_word_division', 'SmcTuring.Appendix.DivisionAlgebra.quotient_fits', 'SmcTuring.Appendix.DivisionRepairs.divisor_copy', 'SmcTuring.Appendix.DivisionRepairs.divisor_copy_register', 'SmcTuring.Appendix.DivisionRepairs.exit_selection', 'SmcTuring.Appendix.DivisionRepairs.exit_delta', 'SmcTuring.Appendix.DivisionRepairs.body_continuation', 'SmcTuring.Appendix.DivisionRepairs.reset_owned_field', 'SmcTuring.Appendix.DivisionRepairs.reset_packet', 'SmcTuring.Appendix.DivisionRepairs.reset_fetch']
    assert set(division_foundation_names) <= {item["name"] for item in declarations}
    report["division_foundation_checked"] = True
    report["checked_division_foundation_declarations"] = division_foundation_names

    division_data_names = ['SmcTuring.Appendix.DivisionSignedAlgebra.sample_sign', 'SmcTuring.Appendix.DivisionSignedAlgebra.sample_mask', 'SmcTuring.Appendix.DivisionSignedAlgebra.sample_xor', 'SmcTuring.Appendix.DivisionSignedAlgebra.borrow_sign', 'SmcTuring.Appendix.DivisionSignedAlgebra.normalize_mask', 'SmcTuring.Appendix.DivisionSignedAlgebra.negative_bit_mask', 'SmcTuring.Appendix.DivisionSignedAlgebra.normalize_negative_mask', 'SmcTuring.Appendix.DivisionSignedAlgebra.apply_sign', 'SmcTuring.Appendix.DivisionSignedAlgebra.absolute_normalization', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_toNat', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_bound', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_nonnegative_small', 'SmcTuring.Appendix.DivisionSignedAlgebra.signed_decomposition', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_nonzero', 'SmcTuring.Appendix.DivisionSignedAlgebra.mathematical_magnitude', 'SmcTuring.Appendix.DivisionSignedAlgebra.result_pattern', 'SmcTuring.Appendix.DivisionSignedAlgebra.quotient_word', 'SmcTuring.Appendix.DivisionSignedAlgebra.remainder_word', 'SmcTuring.Appendix.DivisionSignedAlgebra.result_sdiv', 'SmcTuring.Appendix.DivisionSignedAlgebra.result_srem', 'SmcTuring.Appendix.DivisionSignedAlgebra.result_toInt', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_half_iff', 'SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_not_min', 'SmcTuring.Appendix.DivisionSignedAlgebra.negative_magnitude_one', 'SmcTuring.Appendix.DivisionSignedAlgebra.positive_quotient_small', 'SmcTuring.Appendix.DivisionSignedAlgebra.quotient_range', 'SmcTuring.Appendix.DivisionSignedAlgebra.remainder_range', 'SmcTuring.Appendix.DivisionSignedAlgebra.quotient_toInt', 'SmcTuring.Appendix.DivisionSignedAlgebra.remainder_toInt', 'SmcTuring.Appendix.DivisionWords.field_eq', 'SmcTuring.Appendix.DivisionWords.every_instruction_writes', 'SmcTuring.Appendix.DivisionWords.execute_frame', 'SmcTuring.Appendix.DivisionWords.run_frame', 'SmcTuring.Appendix.DivisionWords.run_append', 'SmcTuring.Appendix.DivisionWords.embedded_run', 'SmcTuring.Appendix.DivisionWords.copy_effect', 'SmcTuring.Appendix.DivisionWords.pure_of_destinations', 'SmcTuring.Appendix.DivisionWords.body_length', 'SmcTuring.Appendix.DivisionWordAlgebra.doubling_borrow', 'SmcTuring.Appendix.DivisionWordAlgebra.masked_double_no_borrow', 'SmcTuring.Appendix.DivisionWordAlgebra.subtract_restore', 'SmcTuring.Appendix.DivisionWordAlgebra.quotient_bit', 'SmcTuring.Appendix.DivisionWordAlgebra.low_add_carry', 'SmcTuring.Appendix.DivisionWordAlgebra.trial_toNat', 'SmcTuring.Appendix.DivisionWordAlgebra.next_high_toNat', 'SmcTuring.Appendix.DivisionWordAlgebra.signed_result_carry', 'SmcTuring.Appendix.DivisionPrefixes.sample_field', 'SmcTuring.Appendix.DivisionPrefixes.sample_accumulator', 'SmcTuring.Appendix.DivisionPrefixes.sample_carry', 'SmcTuring.Appendix.DivisionPrefixes.sign_field', 'SmcTuring.Appendix.DivisionPrefixes.sign_accumulator', 'SmcTuring.Appendix.DivisionPrefixes.sign_carry', 'SmcTuring.Appendix.DivisionPrefixes.masked_normalization', 'SmcTuring.Appendix.DivisionPrefixes.normalize_field', 'SmcTuring.Appendix.DivisionPrefixes.normalize_accumulator', 'SmcTuring.Appendix.DivisionPrefixes.normalize_carry', 'SmcTuring.Appendix.DivisionPrefixes.sign_length', 'SmcTuring.Appendix.DivisionPrefixes.normalize_length', 'SmcTuring.Appendix.DivisionBody.body_field', 'SmcTuring.Appendix.DivisionBody.body_accumulator', 'SmcTuring.Appendix.DivisionBody.body_carry', 'SmcTuring.Appendix.DivisionBody.body_frame', 'SmcTuring.Appendix.DivisionBody.body_pure', 'SmcTuring.Appendix.DivisionBody.body_low', 'SmcTuring.Appendix.DivisionBody.body_high', 'SmcTuring.Appendix.DivisionBody.body_counter', 'SmcTuring.Appendix.DivisionBody.body_divisor', 'SmcTuring.Appendix.DivisionBody.restoring_remainder', 'SmcTuring.Appendix.DivisionStages.signed_initial_shape', 'SmcTuring.Appendix.DivisionStages.initial_field', 'SmcTuring.Appendix.DivisionStages.initial_accumulator', 'SmcTuring.Appendix.DivisionStages.initial_carry', 'SmcTuring.Appendix.DivisionStages.initial_length', 'SmcTuring.Appendix.DivisionStages.finish_field', 'SmcTuring.Appendix.DivisionStages.finish_accumulator', 'SmcTuring.Appendix.DivisionStages.finish_carry', 'SmcTuring.Appendix.DivisionStages.finish_signed_result', 'SmcTuring.Appendix.DivisionStages.finish_length', 'SmcTuring.Appendix.DivisionStages.initial_frame', 'SmcTuring.Appendix.DivisionStages.initial_pure', 'SmcTuring.Appendix.DivisionStages.initial_inputs', 'SmcTuring.Appendix.DivisionStages.finish_frame', 'SmcTuring.Appendix.DivisionStages.finish_pure', 'SmcTuring.Appendix.DivisionStages.finish_signed_carry', 'SmcTuring.Appendix.DivisionPacked.prefix_bound', 'SmcTuring.Appendix.DivisionPacked.quotient_bound', 'SmcTuring.Appendix.DivisionPacked.packed_bit', 'SmcTuring.Appendix.DivisionPacked.packed_shift', 'SmcTuring.Appendix.DivisionPacked.scan_next', 'SmcTuring.Appendix.DivisionPacked.next_low_toNat', 'SmcTuring.Appendix.DivisionPacked.packed_step', 'SmcTuring.Appendix.DivisionIteration.initial_invariant', 'SmcTuring.Appendix.DivisionIteration.advance', 'SmcTuring.Appendix.DivisionIteration.invariant', 'SmcTuring.Appendix.DivisionIteration.correct', 'SmcTuring.Appendix.DivisionIteration.accumulator', 'SmcTuring.Appendix.DivisionIteration.frame', 'SmcTuring.Appendix.DivisionIteration.repeated_execution', 'SmcTuring.Appendix.DivisionIteration.repeated_length', 'SmcTuring.Appendix.DivisionIteration.repeated_pure', 'SmcTuring.Appendix.DivisionDataCorrect.initialized', 'SmcTuring.Appendix.DivisionDataCorrect.divisor_nonzero', 'SmcTuring.Appendix.DivisionDataCorrect.loop_result', 'SmcTuring.Appendix.DivisionDataCorrect.loop_sign', 'SmcTuring.Appendix.DivisionDataCorrect.program_execution', 'SmcTuring.Appendix.DivisionDataCorrect.result_pattern', 'SmcTuring.Appendix.DivisionDataCorrect.signed_quotient', 'SmcTuring.Appendix.DivisionDataCorrect.signed_remainder', 'SmcTuring.Appendix.DivisionDataCorrect.program_accumulator', 'SmcTuring.Appendix.DivisionDataCorrect.pure_append', 'SmcTuring.Appendix.DivisionDataCorrect.program_pure', 'SmcTuring.Appendix.DivisionDataCorrect.program_length', 'SmcTuring.Appendix.DivisionDataCorrect.loop_preserved', 'SmcTuring.Appendix.DivisionDataCorrect.program_inputs', 'SmcTuring.Appendix.DivisionDataCorrect.program_frame', 'SmcTuring.Appendix.DivisionDataCorrect.displacement_reset', 'SmcTuring.Appendix.DivisionDataCorrect.program_carry']
    assert set(division_data_names) <= {item["name"] for item in declarations}
    report["division_data_checked"] = True
    report["checked_division_data_declarations"] = division_data_names

    division_control_names = ['SmcTuring.Appendix.DivisionGuard.binding_injective', 'SmcTuring.Appendix.DivisionGuard.guard_separate', 'SmcTuring.Appendix.DivisionGuard.frame', 'SmcTuring.Appendix.DivisionGuard.field', 'SmcTuring.Appendix.DivisionGuard.accumulator', 'SmcTuring.Appendix.DivisionGuard.carry', 'SmcTuring.Appendix.DivisionGuard.displacement', 'SmcTuring.Appendix.DivisionGuard.pure', 'SmcTuring.Appendix.DivisionGuard.invariant', 'SmcTuring.Appendix.DivisionGuard.length', 'SmcTuring.Appendix.DivisionControl.run_append', 'SmcTuring.Appendix.DivisionControl.pure_append', 'SmcTuring.Appendix.DivisionControl.lift_effect', 'SmcTuring.Appendix.DivisionControl.lift_pure', 'SmcTuring.Appendix.DivisionControl.embed_run', 'SmcTuring.Appendix.DivisionControl.embed_pure', 'SmcTuring.Appendix.DivisionControl.round_trip_effect', 'SmcTuring.Appendix.DivisionControl.round_trip_ready', 'SmcTuring.Appendix.DivisionControl.round_trip_pure', 'SmcTuring.Appendix.DivisionControl.ready_lift', 'SmcTuring.Appendix.DivisionControl.initial_ready', 'SmcTuring.Appendix.DivisionControl.lift_length', 'SmcTuring.Appendix.DivisionControl.round_trip_length', 'SmcTuring.Appendix.DivisionBlocks.delta_value', 'SmcTuring.Appendix.DivisionBlocks.delta_nonzero', 'SmcTuring.Appendix.DivisionBlocks.continuations_distinct', 'SmcTuring.Appendix.DivisionBlocks.literal_lengths', 'SmcTuring.Appendix.DivisionBlocks.words_pure', 'SmcTuring.Appendix.DivisionBlocks.words_frame', 'SmcTuring.Appendix.DivisionBlocks.ready_lift', 'SmcTuring.Appendix.DivisionBlocks.call_separate', 'SmcTuring.Appendix.DivisionBlocks.program_effect', 'SmcTuring.Appendix.DivisionBlocks.program_ready', 'SmcTuring.Appendix.DivisionBlocks.program_frame', 'SmcTuring.Appendix.DivisionBlocks.program_pure', 'SmcTuring.Appendix.DivisionBlocks.clear_guard', 'SmcTuring.Appendix.DivisionBlocks.guard_effect', 'SmcTuring.Appendix.DivisionBlocks.body_effect', 'SmcTuring.Appendix.DivisionBlocks.entry_effect', 'SmcTuring.Appendix.DivisionBlocks.finish_effect', 'SmcTuring.Appendix.DivisionBlocks.words_frame_written', 'SmcTuring.Appendix.DivisionBlocks.program_frame_written', 'SmcTuring.Appendix.DivisionBlocks.program_accumulator', 'SmcTuring.Appendix.DivisionBlocks.program_stack', 'SmcTuring.Appendix.DivisionExecution.finish_invariant', 'SmcTuring.Appendix.DivisionExecution.finish_observations', 'SmcTuring.Appendix.DivisionExecution.exit_finishes', 'SmcTuring.Appendix.DivisionExecution.loop_finishes', 'SmcTuring.Appendix.DivisionExecution.loop_run', 'SmcTuring.Appendix.DivisionExecution.divide_finishes']
    assert set(division_control_names) <= {item["name"] for item in declarations}
    report["division_control_checked"] = True
    report["checked_division_control_declarations"] = division_control_names

    division_complete_word_names = ['SmcTuring.Appendix.DivisionObservations.loop_frame', 'SmcTuring.Appendix.DivisionObservations.loop_pure', 'SmcTuring.Appendix.DivisionObservations.loop_preserves', 'SmcTuring.Appendix.DivisionObservations.source_slots_stable', 'SmcTuring.Appendix.DivisionObservations.divide_pure', 'SmcTuring.Appendix.DivisionObservations.divide_frame', 'SmcTuring.Appendix.DivisionObservations.divide_inputs', 'SmcTuring.Appendix.DivisionObservations.divide_sign', 'SmcTuring.Appendix.DivisionCorrect.selected', 'SmcTuring.Appendix.DivisionCorrect.output', 'SmcTuring.Appendix.DivisionCorrect.carry', 'SmcTuring.Appendix.DivisionCorrect.correct', 'SmcTuring.Appendix.DivisionCorrect.signed_quotient', 'SmcTuring.Appendix.DivisionCorrect.signed_remainder', 'SmcTuring.Appendix.DivisionCorrect.unsigned_quotient', 'SmcTuring.Appendix.DivisionCorrect.unsigned_remainder']
    assert set(division_complete_word_names) <= {item["name"] for item in declarations}
    report["division_complete_word_checked"] = True
    report["checked_division_complete_word_declarations"] = division_complete_word_names

    division_byte_primitives_names = ['SmcTuring.Appendix.DivisionByteCode.common_decode', 'SmcTuring.Appendix.DivisionByteCode.subtract_payload', 'SmcTuring.Appendix.DivisionByteCode.right_payload', 'SmcTuring.Appendix.DivisionByteCode.adc_payload', 'SmcTuring.Appendix.DivisionByteCode.form_roundtrip', 'SmcTuring.Appendix.DivisionByteCode.encode_injective', 'SmcTuring.Appendix.DivisionByteCode.encode_length', 'SmcTuring.Appendix.DivisionByteCode.length_bounds', 'SmcTuring.Appendix.DivisionByteCode.common_length', 'SmcTuring.Appendix.DivisionByteCode.encoded_length', 'SmcTuring.Appendix.DivisionByteCode.length_take_two', 'SmcTuring.Appendix.DivisionByteCode.fetch_current_encoding', 'SmcTuring.Appendix.DivisionByteCode.fetch_written_encoding', 'SmcTuring.Appendix.DivisionByteCode.subtract_patch', 'SmcTuring.Appendix.DivisionByteCode.fetch_patched_subtract', 'SmcTuring.Appendix.DivisionByteCode.fetch_patched_current_subtract', 'SmcTuring.Appendix.DivisionByteExecution.execute_effect', 'SmcTuring.Appendix.DivisionByteExecution.execute_memory', 'SmcTuring.Appendix.DivisionByteExecution.execute_accumulator', 'SmcTuring.Appendix.DivisionByteExecution.execute_stack', 'SmcTuring.Appendix.DivisionByteExecution.execute_carry', 'SmcTuring.Appendix.DivisionByteExecution.execute_pc', 'SmcTuring.Appendix.DivisionByteExecution.written_word', 'SmcTuring.Appendix.DivisionByteExecution.execute_frame', 'SmcTuring.Appendix.DivisionByteExecution.load_frame', 'SmcTuring.Appendix.DivisionByteExecution.footprint_length', 'SmcTuring.Appendix.DivisionByteExecution.footprint_nonempty', 'SmcTuring.Appendix.DivisionByteExecution.common_execution', 'SmcTuring.Appendix.DivisionByteExecution.subtract_carry', 'SmcTuring.Appendix.DivisionByteExecution.right31_carry', 'SmcTuring.Appendix.DivisionByteExecution.adc_zero_value', 'SmcTuring.Appendix.DivisionByteExecution.adc_zero_carry', 'SmcTuring.Appendix.DivisionByteExecution.decrement_preserves_carry', 'SmcTuring.Appendix.DivisionByteExecution.step_current_encoding', 'SmcTuring.Appendix.DivisionByteExecution.step_patched_subtract', 'SmcTuring.Appendix.DivisionByteExecution.trace_run', 'SmcTuring.Appendix.DivisionByteExecution.run_append', 'SmcTuring.Appendix.DivisionByteExecution.trace_append', 'SmcTuring.Appendix.DivisionByteExecution.owned_append', 'SmcTuring.Appendix.DivisionByteExecution.common_run']
    assert set(division_byte_primitives_names) <= {item["name"] for item in declarations}
    report["division_byte_primitives_checked"] = True
    report["checked_division_byte_primitives_declarations"] = division_byte_primitives_names

    division_refinement_names = ['SmcTuring.Appendix.DivisionRefinement.destination_dependency', 'SmcTuring.Appendix.DivisionRefinement.translate_destination', 'SmcTuring.Appendix.DivisionRefinement.translate_value', 'SmcTuring.Appendix.DivisionRefinement.translate_accumulator', 'SmcTuring.Appendix.DivisionRefinement.translate_carry', 'SmcTuring.Appendix.DivisionRefinement.translate_stack', 'SmcTuring.Appendix.DivisionRefinement.translate_length', 'SmcTuring.Appendix.DivisionRefinement.execute_pc', 'SmcTuring.Appendix.DivisionRefinement.execute_read_destination', 'SmcTuring.Appendix.DivisionRefinement.execute_read_frame', 'SmcTuring.Appendix.DivisionRefinement.simulate', 'SmcTuring.Appendix.DivisionRefinement.forms_length', 'SmcTuring.Appendix.DivisionRefinement.forms_run', 'SmcTuring.Appendix.DivisionRefinement.simulate_run', 'SmcTuring.Appendix.DivisionRefinement.run_stack', 'SmcTuring.Appendix.DivisionRefinement.run_frame', 'SmcTuring.Appendix.DivisionRefinement.owned_run']
    assert set(division_refinement_names) <= {item["name"] for item in declarations}
    report["division_refinement_checked"] = True
    report["checked_division_refinement_declarations"] = division_refinement_names

    division_image_names = ['SmcTuring.Appendix.DivisionImage.initial_length', 'SmcTuring.Appendix.DivisionImage.current_length', 'SmcTuring.Appendix.DivisionImage.subtract_words', 'SmcTuring.Appendix.DivisionImage.intact_current', 'SmcTuring.Appendix.DivisionImage.fetch_current', 'SmcTuring.Appendix.DivisionImage.initialized_packet', 'SmcTuring.Appendix.DivisionImage.patch_owner', 'SmcTuring.Appendix.DivisionImage.owned_field_inside', 'SmcTuring.Appendix.DivisionImage.separated_tail', 'SmcTuring.Appendix.DivisionImage.apart_bytes', 'SmcTuring.Appendix.DivisionImage.image_packet', 'SmcTuring.Appendix.DivisionImage.initialized_intact', 'SmcTuring.Appendix.DivisionImage.frame_packet', 'SmcTuring.Appendix.DivisionImage.store_intact', 'SmcTuring.Appendix.DivisionImage.execute_intact']
    assert set(division_image_names) <= {item["name"] for item in declarations}
    report["division_image_checked"] = True
    report["checked_division_image_declarations"] = division_image_names

    division_packets_names = ['SmcTuring.Appendix.DivisionPackets.literal_current', 'SmcTuring.Appendix.DivisionPackets.literal_length', 'SmcTuring.Appendix.DivisionPackets.data_span', 'SmcTuring.Appendix.DivisionPackets.tail_span', 'SmcTuring.Appendix.DivisionPackets.restore_span', 'SmcTuring.Appendix.DivisionPackets.span_append', 'SmcTuring.Appendix.DivisionPackets.packet_span', 'SmcTuring.Appendix.DivisionPackets.packet_count', 'SmcTuring.Appendix.DivisionPackets.inactive_count', 'SmcTuring.Appendix.DivisionPackets.inactive_span']
    assert set(division_packets_names) <= {item["name"] for item in declarations}
    report["division_packets_checked"] = True
    report["checked_division_packets_declarations"] = division_packets_names

    division_byte_execution_names = ['SmcTuring.Appendix.DivisionPacking.size_cons', 'SmcTuring.Appendix.DivisionPacking.size_append', 'SmcTuring.Appendix.DivisionPacking.place_append', 'SmcTuring.Appendix.DivisionPacking.placed_lower', 'SmcTuring.Appendix.DivisionPacking.placed_upper', 'SmcTuring.Appendix.DivisionPacking.placed_separated', 'SmcTuring.Appendix.DivisionPacking.initial_intact', 'SmcTuring.Appendix.DivisionPacking.initial_fetch', 'SmcTuring.Appendix.DivisionPacking.fields_append', 'SmcTuring.Appendix.DivisionPacking.fields_owned', 'SmcTuring.Appendix.DivisionPacking.same_owner_separate', 'SmcTuring.Appendix.DivisionPacking.owned_separate', 'SmcTuring.Appendix.DivisionPacking.field_layout', 'SmcTuring.Appendix.DivisionPacking.placed_field_layout', 'SmcTuring.Appendix.DivisionPacking.image_frame', 'SmcTuring.Appendix.DivisionRegions.member', 'SmcTuring.Appendix.DivisionRegions.entry_bounds', 'SmcTuring.Appendix.DivisionRegions.separated_append', 'SmcTuring.Appendix.DivisionRegions.separated', 'SmcTuring.Appendix.DivisionRegions.capacity', 'SmcTuring.Appendix.DivisionRegions.field_layout', 'SmcTuring.Appendix.DivisionRegions.initial_intact', 'SmcTuring.Appendix.DivisionRegions.image_append', 'SmcTuring.Appendix.DivisionRegions.image_frame', 'SmcTuring.Appendix.DivisionRegions.outside_owned', 'SmcTuring.Appendix.DivisionLinear.span_cons', 'SmcTuring.Appendix.DivisionLinear.minimum_length', 'SmcTuring.Appendix.DivisionLinear.execute_pc', 'SmcTuring.Appendix.DivisionLinear.constructed_trace', 'SmcTuring.Appendix.DivisionLinear.image_trace', 'SmcTuring.Appendix.DivisionLinear.run_pc', 'SmcTuring.Appendix.DivisionLinear.owned_run', 'SmcTuring.Appendix.DivisionLinear.run_intact', 'SmcTuring.Appendix.DivisionLinear.run_common', 'SmcTuring.Appendix.DivisionLayout.data_initial', 'SmcTuring.Appendix.DivisionLayout.data_initials', 'SmcTuring.Appendix.DivisionLayout.tail_initials', 'SmcTuring.Appendix.DivisionLayout.restore_initials', 'SmcTuring.Appendix.DivisionLayout.pure_initials', 'SmcTuring.Appendix.DivisionLayout.pure_size', 'SmcTuring.Appendix.DivisionLayout.data_size', 'SmcTuring.Appendix.DivisionLayout.tail_size', 'SmcTuring.Appendix.DivisionLayout.restore_size', 'SmcTuring.Appendix.DivisionLayout.data_fields', 'SmcTuring.Appendix.DivisionLayout.tail_fields', 'SmcTuring.Appendix.DivisionLayout.restore_fields', 'SmcTuring.Appendix.DivisionLayout.ordered', 'SmcTuring.Appendix.DivisionLayout.capacity', 'SmcTuring.Appendix.DivisionLayout.separated', 'SmcTuring.Appendix.DivisionLayout.field_layout', 'SmcTuring.Appendix.DivisionLayout.initial_intact', 'SmcTuring.Appendix.DivisionLayout.initial_fetch', 'SmcTuring.Appendix.DivisionLayout.pure_fields', 'SmcTuring.Appendix.DivisionLayout.image_fields', 'SmcTuring.Appendix.DivisionLayout.slot_owned', 'SmcTuring.Appendix.DivisionLayout.pointer_owned', 'SmcTuring.Appendix.DivisionLayout.address_owned', 'SmcTuring.Appendix.DivisionLayout.slot_fits', 'SmcTuring.Appendix.DivisionLayout.owned_patch_intact', 'SmcTuring.Appendix.DivisionLayout.written_active', 'SmcTuring.Appendix.DivisionData.span_cons', 'SmcTuring.Appendix.DivisionData.instruction_length', 'SmcTuring.Appendix.DivisionData.current_translation', 'SmcTuring.Appendix.DivisionData.execute_pc', 'SmcTuring.Appendix.DivisionData.constructed_trace', 'SmcTuring.Appendix.DivisionData.image_trace', 'SmcTuring.Appendix.DivisionData.run_pc', 'SmcTuring.Appendix.DivisionData.block_linked', 'SmcTuring.Appendix.DivisionData.block_dependency_owned', 'SmcTuring.Appendix.DivisionData.block_capacity', 'SmcTuring.Appendix.DivisionData.block_placed', 'SmcTuring.Appendix.DivisionData.block_code_fits', 'SmcTuring.Appendix.DivisionData.block_trace', 'SmcTuring.Appendix.DivisionData.block_image_trace', 'SmcTuring.Appendix.DivisionData.run_intact', 'SmcTuring.Appendix.DivisionData.block_intact', 'SmcTuring.Appendix.DivisionData.block_refinement', 'SmcTuring.Appendix.DivisionData.pure_destinations', 'SmcTuring.Appendix.DivisionSetup.call_field_position', 'SmcTuring.Appendix.DivisionSetup.tail_placed', 'SmcTuring.Appendix.DivisionSetup.continuation_placed', 'SmcTuring.Appendix.DivisionSetup.tail_fits', 'SmcTuring.Appendix.DivisionSetup.continuation_fits', 'SmcTuring.Appendix.DivisionSetup.pointer_fits', 'SmcTuring.Appendix.DivisionSetup.address_fits', 'SmcTuring.Appendix.DivisionSetup.call_fits', 'SmcTuring.Appendix.DivisionSetup.slot_alias', 'SmcTuring.Appendix.DivisionSetup.pointer_nonwrap', 'SmcTuring.Appendix.DivisionSetup.slot_apart', 'SmcTuring.Appendix.DivisionSetup.call_apart', 'SmcTuring.Appendix.DivisionSetup.metadata_outside', 'SmcTuring.Appendix.DivisionSetup.run_read_frame', 'SmcTuring.Appendix.DivisionSetup.data_read_frame', 'SmcTuring.Appendix.DivisionSetup.data_ready', 'SmcTuring.Appendix.DivisionSetup.stack_placed', 'SmcTuring.Appendix.DivisionSetup.initial_ready', 'SmcTuring.Appendix.DivisionSetup.single_owner_placed', 'SmcTuring.Appendix.DivisionSetup.initial_mov', 'SmcTuring.Appendix.DivisionSetup.initial_operands', 'SmcTuring.Appendix.DivisionSetup.call_placed', 'SmcTuring.Appendix.DivisionSetup.call_entry_initial', 'SmcTuring.Appendix.DivisionSetup.initial_call', 'SmcTuring.Appendix.DivisionSetup.fixed_call', 'SmcTuring.Appendix.DivisionSetup.word_separate', 'SmcTuring.Appendix.DivisionSetup.control_separate', 'SmcTuring.Appendix.DivisionSetup.continuation_code', 'SmcTuring.Appendix.DivisionPaths.tail_run', 'SmcTuring.Appendix.DivisionPaths.restore_run', 'SmcTuring.Appendix.DivisionPaths.forms_run', 'SmcTuring.Appendix.DivisionPaths.fetched_current', 'SmcTuring.Appendix.DivisionPaths.call_current', 'SmcTuring.Appendix.DivisionPaths.tail_trace_intact', 'SmcTuring.Appendix.DivisionPaths.tail_owned', 'SmcTuring.Appendix.DivisionPaths.continuation_ownership', 'SmcTuring.Appendix.DivisionPaths.continuation_straight', 'SmcTuring.Appendix.DivisionPaths.continuation_span', 'SmcTuring.Appendix.DivisionPaths.continuation_trace', 'SmcTuring.Appendix.DivisionPaths.continuation_intact', 'SmcTuring.Appendix.DivisionPaths.continued_effect', 'SmcTuring.Appendix.DivisionPaths.continued_ready', 'SmcTuring.Appendix.DivisionPaths.continued_intact', 'SmcTuring.Appendix.DivisionPaths.tail_target_pc', 'SmcTuring.Appendix.DivisionPaths.continued_trace', 'SmcTuring.Appendix.DivisionPaths.continued_owned', 'SmcTuring.Appendix.DivisionByteBlocks.view_agreement', 'SmcTuring.Appendix.DivisionByteBlocks.forms_run', 'SmcTuring.Appendix.DivisionByteBlocks.data_end_pc', 'SmcTuring.Appendix.DivisionByteBlocks.guard_displacement', 'SmcTuring.Appendix.DivisionByteBlocks.target', 'SmcTuring.Appendix.DivisionByteBlocks.run_effect', 'SmcTuring.Appendix.DivisionByteBlocks.trace', 'SmcTuring.Appendix.DivisionByteBlocks.image_trace', 'SmcTuring.Appendix.DivisionByteBlocks.run_intact', 'SmcTuring.Appendix.DivisionByteBlocks.run_ready', 'SmcTuring.Appendix.DivisionByteBlocks.owned', 'SmcTuring.Appendix.DivisionByteBlocks.refinement', 'SmcTuring.Appendix.DivisionByteBlocks.run_pc', 'SmcTuring.Appendix.DivisionByteBlocks.field', 'SmcTuring.Appendix.DivisionByteBlocks.stack', 'SmcTuring.Appendix.DivisionByteSimulation.view_agreement', 'SmcTuring.Appendix.DivisionByteSimulation.slot_word', 'SmcTuring.Appendix.DivisionByteSimulation.source_ready', 'SmcTuring.Appendix.DivisionByteSimulation.continued_pc', 'SmcTuring.Appendix.DivisionByteSimulation.end_code', 'SmcTuring.Appendix.DivisionByteSimulation.block_start', 'SmcTuring.Appendix.DivisionByteSimulation.guard_ready', 'SmcTuring.Appendix.DivisionByteSimulation.source_data_effect', 'SmcTuring.Appendix.DivisionByteSimulation.source_stack_effect', 'SmcTuring.Appendix.DivisionByteSimulation.block', 'SmcTuring.Appendix.DivisionByteSimulation.advance', 'SmcTuring.Appendix.DivisionByteLoop.loop_step', 'SmcTuring.Appendix.DivisionByteLoop.entry_location', 'SmcTuring.Appendix.DivisionByteLoop.body_boundary', 'SmcTuring.Appendix.DivisionByteLoop.exit_simulate', 'SmcTuring.Appendix.DivisionByteLoop.simulate', 'SmcTuring.Appendix.DivisionByteCorrect.maintained_context', 'SmcTuring.Appendix.DivisionByteCorrect.context_execution', 'SmcTuring.Appendix.DivisionByteCorrect.context_correct', 'SmcTuring.Appendix.DivisionByteCorrect.reusable_correct', 'SmcTuring.Appendix.DivisionByteCorrect.initial_context', 'SmcTuring.Appendix.DivisionByteCorrect.divide_simulate', 'SmcTuring.Appendix.DivisionByteCorrect.execution', 'SmcTuring.Appendix.DivisionByteCorrect.owned_run_frame', 'SmcTuring.Appendix.DivisionByteCorrect.trace_frame', 'SmcTuring.Appendix.DivisionByteCorrect.field_cases', 'SmcTuring.Appendix.DivisionByteCorrect.correct', 'SmcTuring.Appendix.DivisionByteCorrect.signed_quotient', 'SmcTuring.Appendix.DivisionByteCorrect.signed_remainder', 'SmcTuring.Appendix.DivisionByteCorrect.unsigned_quotient', 'SmcTuring.Appendix.DivisionByteCorrect.unsigned_remainder']
    assert set(division_byte_execution_names) <= {item["name"] for item in declarations}
    report["division_byte_execution_checked"] = True
    report["checked_division_byte_execution_declarations"] = division_byte_execution_names

    branch_geometry_names = ['SmcTuring.Appendix.ByteRegions.separated_append_disjoint', 'SmcTuring.Appendix.ByteRegions.separated_disjoint', 'SmcTuring.Appendix.SpacedLayout.valid_checks', 'SmcTuring.Appendix.SpacedLayout.ordered_valid', 'SmcTuring.Appendix.SpacedLayout.regions_disjoint', 'SmcTuring.Appendix.SpacedControl.prefix_disjoint_frame', 'SmcTuring.Appendix.SpacedLayout.separated', 'SmcTuring.Appendix.SpacedLayout.full_layout', 'SmcTuring.Appendix.SpacedLayout.separate_fields', 'SmcTuring.Appendix.SpacedPrefix.trace', 'SmcTuring.Appendix.SpacedPrefix.initialized_displacement', 'SmcTuring.Appendix.SpacedControl.prefix_stack', 'SmcTuring.Appendix.SpacedPaths.tail_trace_intact', 'SmcTuring.Appendix.SpacedWhole.correct', 'SmcTuring.Appendix.SpacedWhole.gap_frame']
    assert set(branch_geometry_names) <= {item["name"] for item in declarations}
    report["appendix_branch_geometry_checked"] = True
    report["checked_appendix_branch_geometry_declarations"] = branch_geometry_names
    terminal_names = ['SmcTuring.Native.ByteMemory.put_current', 'SmcTuring.Native.DwordStore.roundtrip', 'SmcTuring.Native.DwordStore.length', 'SmcTuring.Native.DwordStore.encode_injective', 'SmcTuring.Native.DwordStore.fetch_encoding', 'SmcTuring.Native.DwordStore.step_encoding', 'SmcTuring.Native.DwordStore.registers', 'SmcTuring.Native.DwordStore.pc', 'SmcTuring.Native.DwordStore.memory', 'SmcTuring.Native.DwordStore.frame', 'SmcTuring.Native.DwordStore.written', 'SmcTuring.Native.DwordStore.writes', 'SmcTuring.Native.DwordStore.emit_address', 'SmcTuring.Native.TerminalMarker.length', 'SmcTuring.Native.TerminalMarker.reach', 'SmcTuring.Native.TerminalMarker.displacement_x64', 'SmcTuring.Native.TerminalMarker.target', 'SmcTuring.Native.TerminalMarker.target_toNat', 'SmcTuring.Native.TerminalMarker.current_image', 'SmcTuring.Native.TerminalMarker.current_immediate', 'SmcTuring.Native.TerminalMarker.memory_unchanged', 'SmcTuring.Native.TerminalMarker.next_position', 'SmcTuring.Native.TerminalMarker.owned_write', 'SmcTuring.Native.TerminalMarker.pure', 'SmcTuring.Native.TerminalMarker.correct', 'SmcTuring.Native.TerminalMarker.reusable', 'SmcTuring.Native.TerminalMarker.output_preserved']
    assert set(terminal_names) <= {item["name"] for item in declarations}
    report["terminal_marker_checked"] = True
    report["checked_terminal_marker_declarations"] = terminal_names

    accumulator_names = ['SmcTuring.Native.AccumulatorLayout.lengths', 'SmcTuring.Native.AccumulatorLayout.save_toNat', 'SmcTuring.Native.AccumulatorLayout.pointer_toNat', 'SmcTuring.Native.AccumulatorLayout.save_next', 'SmcTuring.Native.AccumulatorLayout.first_next', 'SmcTuring.Native.AccumulatorLayout.second_next', 'SmcTuring.Native.AccumulatorLayout.third_next', 'SmcTuring.Native.AccumulatorLayout.save_hits', 'SmcTuring.Native.AccumulatorLayout.first_hits', 'SmcTuring.Native.AccumulatorLayout.second_hits', 'SmcTuring.Native.AccumulatorLayout.third_hits', 'SmcTuring.Native.AccumulatorLayout.save_pointer_apart', 'SmcTuring.Native.AccumulatorEffects.state_ext', 'SmcTuring.Native.AccumulatorEffects.save_effect', 'SmcTuring.Native.AccumulatorEffects.saved_value', 'SmcTuring.Native.AccumulatorEffects.saved_pointer', 'SmcTuring.Native.AccumulatorEffects.swapped_pc', 'SmcTuring.Native.AccumulatorEffects.restored_pc', 'SmcTuring.Native.AccumulatorEffects.restored_memory', 'SmcTuring.Native.AccumulatorEffects.restored_accumulator', 'SmcTuring.Native.AccumulatorEffects.restored_effect', 'SmcTuring.Native.AccumulatorEffects.effect', 'SmcTuring.Native.AccumulatorEffects.correct', 'SmcTuring.Native.AccumulatorEffects.reset_value', 'SmcTuring.Native.AccumulatorEffects.pointer_value', 'SmcTuring.Native.AccumulatorEffects.frame', 'SmcTuring.Native.AccumulatorImage.save_address', 'SmcTuring.Native.AccumulatorImage.first_address', 'SmcTuring.Native.AccumulatorImage.second_address', 'SmcTuring.Native.AccumulatorImage.third_address', 'SmcTuring.Native.AccumulatorImage.supported_run', 'SmcTuring.Native.AccumulatorImage.saved_intact', 'SmcTuring.Native.AccumulatorImage.swapped_intact', 'SmcTuring.Native.AccumulatorImage.restored_intact', 'SmcTuring.Native.AccumulatorImage.finish_intact', 'SmcTuring.Native.AccumulatorImage.fetched', 'SmcTuring.Native.AccumulatorImage.save_trace', 'SmcTuring.Native.AccumulatorImage.trace', 'SmcTuring.Native.AccumulatorImage.owner_value', 'SmcTuring.Native.AccumulatorImage.owner_owned', 'SmcTuring.Native.AccumulatorImage.load_agreement', 'SmcTuring.Native.AccumulatorFinalization.terminal_current', 'SmcTuring.Native.AccumulatorFinalization.terminal_correct', 'SmcTuring.Native.AccumulatorFinalization.memory_effect', 'SmcTuring.Native.AccumulatorFinalization.output_frame', 'SmcTuring.Native.AccumulatorFinalization.live_reuse', 'SmcTuring.Native.AccumulatorFinalization.surround', 'SmcTuring.Native.AccumulatorFinalization.surrounding_pure', 'SmcTuring.Native.AccumulatorFinalization.original_prologue']
    assert set(accumulator_names) <= {item["name"] for item in declarations}
    report["accumulator_finalization_checked"] = True
    report["checked_accumulator_finalization_declarations"] = accumulator_names

    input_operand_names = ['SmcTuring.Appendix.InputOperand.source_length', 'SmcTuring.Appendix.InputOperand.target_length', 'SmcTuring.Appendix.InputOperand.target_roundtrip', 'SmcTuring.Appendix.InputOperand.read_payload', 'SmcTuring.Appendix.InputOperand.current_source', 'SmcTuring.Appendix.InputOperand.current_source_load', 'SmcTuring.Appendix.InputOperand.target_patch', 'SmcTuring.Appendix.InputOperand.patched_target', 'SmcTuring.Appendix.InputOperand.copy_correct', 'SmcTuring.Appendix.InputOperand.copy_frame', 'SmcTuring.Appendix.InputOperand.copy_pure', 'SmcTuring.Appendix.InputOperand.operand_windows', 'SmcTuring.Appendix.InputOperand.word_effect', 'SmcTuring.Appendix.InputOperand.word_symbol']
    input_operand_names.append("SmcTuring.Appendix.InputOperand.source_code_frame")
    assert set(input_operand_names) <= {item["name"] for item in declarations}
    report["input_operand_checked"] = True
    report["checked_input_operand_declarations"] = input_operand_names

    dword_owner_names = ['SmcTuring.Native.DwordOwner.length', 'SmcTuring.Native.DwordOwner.reach', 'SmcTuring.Native.DwordOwner.displacement_x64', 'SmcTuring.Native.DwordOwner.target', 'SmcTuring.Native.DwordOwner.target_toNat', 'SmcTuring.Native.DwordOwner.current_image', 'SmcTuring.Native.DwordOwner.current_immediate', 'SmcTuring.Native.DwordOwner.memory_unchanged', 'SmcTuring.Native.DwordOwner.next_position', 'SmcTuring.Native.DwordOwner.owned_write', 'SmcTuring.Native.DwordOwner.pure', 'SmcTuring.Native.DwordOwner.correct', 'SmcTuring.Native.DwordOwner.reusable', 'SmcTuring.Native.DwordOwner.output_preserved', 'SmcTuring.Native.DwordOwner.patch_value', 'SmcTuring.Native.DwordOwner.patched_current', 'SmcTuring.Native.DwordOwner.initial_zero']
    assert set(dword_owner_names) <= {item["name"] for item in declarations}
    report["dword_owner_checked"] = True
    report["checked_dword_owner_declarations"] = dword_owner_names

    dword_copy_names = ['SmcTuring.Native.DwordCode.roundtrip', 'SmcTuring.Native.DwordCode.encode_injective', 'SmcTuring.Native.DwordCode.encode_length', 'SmcTuring.Native.DwordCode.length_bound', 'SmcTuring.Native.DwordCode.current_header', 'SmcTuring.Native.DwordCode.fetch_encoding', 'SmcTuring.Native.DwordCode.put_word', 'SmcTuring.Native.DwordCode.put_overwrite', 'SmcTuring.Native.DwordCode.put_commute', 'SmcTuring.Native.DwordCode.lift_toNat', 'SmcTuring.Native.DwordCode.low_lift', 'SmcTuring.Native.DwordCode.lift_low_x86', 'SmcTuring.Native.DwordCode.lift_low_x64_bound', 'SmcTuring.Native.DwordCode.read_total', 'SmcTuring.Native.DwordCode.get_put', 'SmcTuring.Native.DwordCode.put_get_back', 'SmcTuring.Native.DwordCode.get_frame', 'SmcTuring.Native.DwordCode.step_encoding', 'SmcTuring.Native.DwordCode.memory', 'SmcTuring.Native.DwordCode.preserved', 'SmcTuring.Native.DwordCode.frame', 'SmcTuring.Native.DwordCode.write_nonempty', 'SmcTuring.Native.DwordLayout.lengths', 'SmcTuring.Native.DwordLayout.endpoint', 'SmcTuring.Native.DwordLayout.span_sizes', 'SmcTuring.Native.DwordLayout.source_toNat', 'SmcTuring.Native.DwordLayout.destination_toNat', 'SmcTuring.Native.DwordLayout.next_nat', 'SmcTuring.Native.DwordLayout.first_next', 'SmcTuring.Native.DwordLayout.second_next', 'SmcTuring.Native.DwordLayout.third_next', 'SmcTuring.Native.DwordLayout.first_hits', 'SmcTuring.Native.DwordLayout.second_hits', 'SmcTuring.Native.DwordLayout.third_hits', 'SmcTuring.Native.DwordLayout.source_outside', 'SmcTuring.Native.DwordLayout.destination_outside', 'SmcTuring.Native.DwordLayout.reachable_iff', 'SmcTuring.Native.DwordLayout.checks_valid', 'SmcTuring.Native.DwordEffects.first_effect', 'SmcTuring.Native.DwordEffects.second_effect', 'SmcTuring.Native.DwordEffects.third_effect', 'SmcTuring.Native.DwordEffects.swapped_pc', 'SmcTuring.Native.DwordEffects.stored_effect', 'SmcTuring.Native.DwordEffects.stored_pc', 'SmcTuring.Native.DwordEffects.original_source_read', 'SmcTuring.Native.DwordEffects.source_read_after_stored', 'SmcTuring.Native.DwordEffects.restored_memory', 'SmcTuring.Native.DwordEffects.effect', 'SmcTuring.Native.DwordEffects.destination_value', 'SmcTuring.Native.DwordEffects.source_value', 'SmcTuring.Native.DwordEffects.frame', 'SmcTuring.Native.DwordEffects.registers', 'SmcTuring.Native.DwordEffects.x86_accumulator', 'SmcTuring.Native.DwordEffects.x64_zero_extension', 'SmcTuring.Native.DwordImage.byte_bindings', 'SmcTuring.Native.DwordImage.placed_entries', 'SmcTuring.Native.DwordImage.size_span', 'SmcTuring.Native.DwordImage.separated', 'SmcTuring.Native.DwordImage.initial_intact', 'SmcTuring.Native.DwordImage.packet_bounds', 'SmcTuring.Native.DwordImage.intact_put', 'SmcTuring.Native.DwordImage.swapped_intact', 'SmcTuring.Native.DwordImage.stored_intact', 'SmcTuring.Native.DwordImage.finish_intact', 'SmcTuring.Native.DwordImage.first_fetch', 'SmcTuring.Native.DwordImage.second_fetch', 'SmcTuring.Native.DwordImage.third_fetch', 'SmcTuring.Native.DwordImage.trace', 'SmcTuring.Native.DwordImage.supported_run', 'SmcTuring.Native.DwordImage.correct', 'SmcTuring.Native.DwordImage.original_correct', 'SmcTuring.Native.DwordImage.image_frame', 'SmcTuring.Native.DwordImage.initial_field', 'SmcTuring.Appendix.InputDword.current_source_word', 'SmcTuring.Appendix.InputDword.copy_correct', 'SmcTuring.Appendix.InputDword.copy_pure', 'SmcTuring.Appendix.InputDword.source_code_frame']
    assert set(dword_copy_names) <= {item["name"] for item in declarations}
    report["dword_copy_checked"] = True
    report["checked_dword_copy_declarations"] = dword_copy_names

    dword_arithmetic_names = ['SmcTuring.Native.DwordArithmetic.two_words', 'SmcTuring.Native.DwordArithmetic.roundtrip', 'SmcTuring.Native.DwordArithmetic.encode_injective', 'SmcTuring.Native.DwordArithmetic.encode_length', 'SmcTuring.Native.DwordArithmetic.header_size', 'SmcTuring.Native.DwordArithmetic.fetch_encoding', 'SmcTuring.Native.DwordArithmetic.step_encoding', 'SmcTuring.Native.DwordArithmetic.registers', 'SmcTuring.Native.DwordArithmetic.written', 'SmcTuring.Native.DwordArithmetic.frame', 'SmcTuring.Native.DwordArithmetic.payload_patch', 'SmcTuring.Native.DwordArithmetic.base_xor_patch', 'SmcTuring.Native.DwordArithmetic.relocate_length', 'SmcTuring.Native.DwordArithmetic.relocate_result', 'SmcTuring.Native.DwordArithmetic.relocate_flag', 'SmcTuring.Native.DwordArithmetic.located_next', 'SmcTuring.Native.DwordArithmetic.located_address', 'SmcTuring.Native.DwordArithmetic.located_effect', 'SmcTuring.Native.DwordArithmetic.write_nonempty']
    assert set(dword_arithmetic_names) <= {item["name"] for item in declarations}
    report["dword_arithmetic_checked"] = True
    report["checked_dword_arithmetic_declarations"] = dword_arithmetic_names

    dword_comparison_names = ['SmcTuring.Appendix.DwordComparison.length', 'SmcTuring.Appendix.DwordComparison.initially_intact', 'SmcTuring.Appendix.DwordComparison.packet_window', 'SmcTuring.Appendix.DwordComparison.current_packet', 'SmcTuring.Appendix.DwordComparison.intact_put', 'SmcTuring.Appendix.DwordComparison.scalar_apart', 'SmcTuring.Appendix.DwordComparison.mask_apart', 'SmcTuring.Appendix.DwordComparison.located_effect', 'SmcTuring.Appendix.DwordComparison.reset_effect', 'SmcTuring.Appendix.DwordComparison.subtracted_effect', 'SmcTuring.Appendix.DwordComparison.negated_effect', 'SmcTuring.Appendix.DwordComparison.borrowed_effect', 'SmcTuring.Appendix.DwordComparison.finish_effect', 'SmcTuring.Appendix.DwordComparison.intermediate_intact', 'SmcTuring.Appendix.DwordComparison.trace', 'SmcTuring.Appendix.DwordComparison.difference_zero', 'SmcTuring.Appendix.DwordComparison.mask_value', 'SmcTuring.Appendix.DwordComparison.memory_effect', 'SmcTuring.Appendix.DwordComparison.frame', 'SmcTuring.Appendix.DwordComparison.owned_destinations', 'SmcTuring.Appendix.DwordComparison.correct', 'SmcTuring.Appendix.DwordComparison.original_correct', 'SmcTuring.Appendix.DwordComparison.pure', 'SmcTuring.Appendix.DwordComparison.checks_valid']
    assert set(dword_comparison_names) <= {item["name"] for item in declarations}
    report["dword_comparison_checked"] = True
    report["checked_dword_comparison_declarations"] = dword_comparison_names

    input_selection_names = ['SmcTuring.Appendix.InputSelection.chosen_difference', 'SmcTuring.Appendix.InputSelection.selected_symbol', 'SmcTuring.Appendix.InputSelection.current_patch', 'SmcTuring.Appendix.InputSelection.xor_then_and', 'SmcTuring.Appendix.InputSelection.tape_target', 'SmcTuring.Appendix.InputSelection.tape_effect', 'SmcTuring.Appendix.InputSelection.tape_step', 'SmcTuring.Appendix.InputSelection.tape_code_frame', 'SmcTuring.Appendix.InputSelection.tape_owned_write', 'SmcTuring.Appendix.InputSelection.comparison_selection']
    assert set(input_selection_names) <= {item["name"] for item in declarations}
    report["input_selection_checked"] = True
    report["checked_input_selection_declarations"] = input_selection_names

    new_names = re.findall(r"^#print axioms (\S+)",(PROJECT/"AuditCursor.lean").read_text(encoding="utf-8"),re.MULTILINE)
    new_names += re.findall(r"^#print axioms (\S+)",(PROJECT/"AuditInputUpdate.lean").read_text(encoding="utf-8"),re.MULTILINE)
    assert set(new_names)<={item["name"] for item in declarations}
    report["cursor_input_update_checked"]=True
    report["checked_cursor_input_update_declarations"]=new_names
    report["passed"] = True
    (ROOT / "validation/lean.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    metadata_path = ROOT / "validation/mathlib.json"
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    assert metadata["revision"] == report["dependency_revision"]
    adapter_names = ["SmcTuring.MathlibTM0." + name for name in [
        "compiler_respects", "standard_halts_iff", "fixed_smc_mathlib_simulation", "standard_terminal_output",
        "Reverse.compiler_respects", "Reverse.labels_card", "Reverse.halts_iff", "Reverse.terminal_output"]]
    assert set(adapter_names) <= {item["name"] for item in declarations}
    metadata["adapter_checked"] = True
    metadata["checked_adapter_direction"] = "Both directions between finite write/move TM and Mathlib TM0; TM0 to pure SMC"
    metadata["checked_adapter_declarations"] = adapter_names
    metadata["reverse_adapter_checked"] = True
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print("Lean build and axiom audit passed.", flush=True)


if __name__ == "__main__":
    main()
