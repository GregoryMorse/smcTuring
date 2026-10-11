"""Check that recorded proof/native evidence matches the current workspace."""
from pathlib import Path
import hashlib
import json
import re
from lean_build import lake_command
from memory_budget import require_budget

ROOT = Path(__file__).resolve().parents[1]

_HASHES={}
def digest(name):
    path=(ROOT/name).resolve()
    if path not in _HASHES:
        h=hashlib.sha256()
        with path.open('rb') as stream:
            for chunk in iter(lambda:stream.read(1<<20),b''):h.update(chunk)
        _HASHES[path]=h.hexdigest()
    return _HASHES[path]

def main():
    require_budget()
    lean = json.loads((ROOT/'validation/lean.json').read_text(encoding='utf-8'))
    assert lean['passed']
    project = ROOT/'lean'
    inventory = list(project.glob('*.lean')) + list((project/'SmcTuring').rglob('*.lean'))
    inventory += [project/name for name in ['lean-toolchain','lakefile.toml','lakefile.proof.toml','lake-manifest.json']]
    inventory += [ROOT/name for name in ['validation/lean_build.py','validation/run_lean.py','validation/bounded_build.py',
      'validation/bounded_audit.py','validation/bounded_snapshot.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py']]
    assert lean['build_config']=='lean/lakefile.proof.toml'
    lake_command(project, Path('.'))
    assert {str(path.relative_to(ROOT)) for path in inventory}==set(lean['sources']), 'Lean source inventory changed'
    for name, expected in lean['sources'].items():
        assert digest(name)==expected, 'Stale Lean source: '+name
    for name, expected in lean['dependency_sources'].items():
        assert digest(name)==expected, 'Stale dependency source: '+name
    from bounded_build import CHAIN,COMMIT,imports_of
    build=lean['bounded_build']
    assert build['passed'] and build['toolchain']==CHAIN and COMMIT in build['version']
    closure=set()
    def visit(module):
        if module in closure:return
        closure.add(module)
        source=project/(module.replace('.','/')+'.lean')
        for dependency in imports_of(source.read_text(encoding='utf-8')):
            if dependency=='SmcTuring' or dependency.startswith('SmcTuring.'):visit(dependency)
    visit('SmcTuring')
    assert closure==set(build['modules']),'Whole-build dependency closure differs'
    for module,record in build['modules'].items():
        relative=module.replace('.','/')
        assert digest(project/(relative+'.lean'))==record['source']
        assert digest(project/'.lake/proof-build/ir'/(relative+'.setup.json'))==record['setup_sha256']
        for path,expected in record['artifacts'].items():assert digest(path)==expected,'Stale checked module: '+path
    for group in ['context','import_header_sources']:
        for path,expected in build[group].items():assert digest(path)==expected,'Stale bounded build input: '+path
    for files in build['external_artifacts'].values():
        for path,expected in files.items():assert digest(path)==expected,'Stale bounded imported artifact: '+path
    declarations = [item['name'] for item in lean['declarations']]
    assert len(set(declarations))==len(declarations), 'Duplicate theorem audit'
    assert lean['converse_checked']
    assert set(lean['checked_converse_declarations']) <= set(declarations)
    assert 'SmcTuring.SMC.Effective.terminal_search_pure_smc' in lean['checked_converse_declarations']
    assert lean['selected_encoding_checked']
    assert set(lean['checked_encoding_declarations']) <= set(declarations)
    assert lean['guard_arithmetic_checked']
    assert set(lean['checked_arithmetic_declarations']) <= set(declarations)
    assert lean['selected_execution_projection_checked']
    assert set(lean['checked_execution_declarations']) <= set(declarations)
    assert lean['automatic_fetch_checked']
    assert set(lean['checked_fetch_declarations']) <= set(declarations)
    assert lean['byte_reader_checked']
    assert set(lean['checked_reader_declarations']) <= set(declarations)
    assert lean['native_call_contracts_checked']
    assert set(lean['checked_native_call_declarations']) <= set(declarations)
    assert lean['native_read_callee_checked']
    assert set(lean['checked_native_read_callee_declarations']) <= set(declarations)
    assert lean['native_storage_grid_checked']
    assert set(lean['checked_native_storage_grid_declarations']) <= set(declarations)
    assert lean['native_combined_image_checked']
    assert set(lean['checked_native_combined_image_declarations']) <= set(declarations)
    assert lean['native_reader_image_checked']
    assert set(lean['checked_native_reader_image_declarations']) <= set(declarations)
    assert lean['native_relocation_checked']
    assert set(lean['checked_native_relocation_declarations']) <= set(declarations)
    assert lean['native_fragment_view_checked']
    assert set(lean['checked_native_fragment_view_declarations']) <= set(declarations)
    assert lean['native_placed_calls_checked']
    assert set(lean['checked_native_placed_calls_declarations']) <= set(declarations)
    assert lean['native_placed_read_callee_checked']
    assert set(lean['checked_native_placed_read_callee_declarations']) <= set(declarations)
    assert lean['native_read_invocation_checked']
    assert set(lean['checked_native_read_invocation_declarations']) <= set(declarations)
    assert lean['native_store_callee_checked']
    assert set(lean['checked_native_store_callee_declarations']) <= set(declarations)
    assert lean['native_store_invocation_checked']
    assert set(lean['checked_native_store_invocation_declarations']) <= set(declarations)
    assert lean['native_spaced_image_checked']
    assert set(lean['checked_native_spaced_image_declarations']) <= set(declarations)
    assert lean['native_aligned_packing_checked']
    assert set(lean['checked_native_aligned_packing_declarations']) <= set(declarations)
    assert lean['native_scalar_image_checked']
    assert set(lean['checked_native_scalar_image_declarations']) <= set(declarations)
    assert lean['native_borrow_mask_checked']
    assert set(lean['checked_native_borrow_mask_declarations']) <= set(declarations)
    assert lean['native_guard_setup_checked']
    assert set(lean['checked_native_guard_setup_declarations']) <= set(declarations)
    assert lean['native_read_scalar_checked']
    assert set(lean['checked_native_read_scalar_declarations']) <= set(declarations)
    assert lean['native_guard_selection_checked']
    assert set(lean['checked_native_guard_selection_declarations']) <= set(declarations)
    assert lean['native_guard_image_checked']
    assert set(lean['checked_native_guard_image_declarations']) <= set(declarations)
    assert lean['native_guard_invocation_checked']
    assert set(lean['checked_native_guard_invocation_declarations']) <= set(declarations)
    assert lean['native_program_composition_checked']
    assert set(lean['checked_native_program_composition_declarations']) <= set(declarations)
    assert lean['native_loop_image_checked']
    assert set(lean['checked_native_loop_image_declarations']) <= set(declarations)
    assert lean['native_kernel_schedule_checked']
    assert set(lean['checked_native_kernel_schedule_declarations']) <= set(declarations)
    assert lean['native_kernel_packets_checked']
    assert set(lean['checked_native_kernel_packets_declarations']) <= set(declarations)
    assert lean['native_guard_packets_checked']
    assert set(lean['checked_native_guard_packets_declarations']) <= set(declarations)
    assert lean['native_source_values_checked']
    assert set(lean['checked_native_source_values_declarations']) <= set(declarations)
    assert lean['native_source_data_checked']
    assert set(lean['checked_native_source_data_declarations']) <= set(declarations)
    assert lean['native_immediate_image_checked']
    assert set(lean['checked_native_immediate_image_declarations']) <= set(declarations)
    assert lean['native_offset_guard_checked']
    assert set(lean['checked_native_offset_guard_declarations']) <= set(declarations)
    for stem in ['pointer_image','address_image','computed_pointer','source_write','load_image','store_image']:
        assert lean['native_'+stem+'_checked']
        assert set(lean['checked_native_'+stem+'_declarations']) <= set(declarations)
    for stem in ['aligned_templates', 'aligned_pool', 'role_initialization', 'byte_lengths', 'metadata_geometry', 'layout_pass', 'emitted_image', 'image_initialization']:
        assert lean['native_'+stem+'_checked']
        assert set(lean['checked_native_'+stem+'_declarations']) <= set(declarations)
    for stem in ['recontext', 'pool_geometry', 'bounded_initialization', 'assembly', 'guard_placement', 'role_separation', 'readiness_atoms', 'guard_readiness', 'loop_initialization']:
        assert lean['native_'+stem+'_checked']
        assert set(lean['checked_native_'+stem+'_declarations']) <= set(declarations)
    for stem in ['compiled_layout', 'invocation_readiness', 'source_separation', 'source_readiness', 'program_certificate']:
        assert lean['native_'+stem+'_checked']
        assert set(lean['checked_native_'+stem+'_declarations']) <= set(declarations)
    for stem in ['memory_region', 'region_execution', 'loaded_execution', 'finite_footprint', 'program_loaded']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['window_bounds', 'reader_bounds', 'calls_bounds', 'read_callee_bounds', 'read_invocation_bounds', 'scalar_bounds', 'read_scalar_bounds', 'allocation']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['placed_bounds', 'borrow_mask_bounds', 'guard_setup_bounds', 'guard_selection_bounds', 'guard_bounds', 'guard_invocation_bounds', 'guard_allocation']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['source_access', 'offset_guard_bounds', 'pointer_bounds', 'address_bounds', 'store_callee_bounds', 'store_invocation_bounds', 'immediate_bounds', 'load_bounds', 'store_bounds', 'block_bounds', 'source_allocation', 'program_bounds', 'program_allocation']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['address_space', 'mapped_execution', 'program_mapped']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['control_bounds', 'program_control']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['program_endpoint', 'source_endpoint', 'checked_execution', 'source_checked']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    for stem in ['loop_bounds', 'program_iteration', 'source_iteration']:
        assert lean["native_"+stem+"_checked"]
        assert set(lean["checked_native_"+stem+"_declarations"]) <= set(declarations)
    assert lean['x64_half_words_checked']
    assert set(lean['checked_x64_half_words_declarations']) <= set(declarations)
    assert lean['x64_half_frame_checked']
    assert len(lean['checked_x64_half_frame_declarations'])==28
    assert set(lean['checked_x64_half_frame_declarations']) <= set(declarations)
    for stem in ['machine32', 'branch_algebra', 'branching', 'branch_tail', 'byte_code', 'byte_execution', 'field_refinement', 'branch_execution', 'byte_image', 'byte_packing', 'byte_program', 'branch_layout', 'branch_prefix', 'byte_control', 'byte_linear', 'branch_control', 'branch_paths', 'branch_whole', 'byte_regions', 'spaced_layout', 'spaced_prefix', 'spaced_control', 'spaced_paths', 'spaced_whole', 'multiply_algebra', 'multiply_words', 'multiply_loop', 'multiply_control', 'multiply_blocks', 'multiply_execution']:
        assert lean['appendix_'+stem+'_checked']
        assert set(lean['checked_appendix_'+stem+'_declarations']) <= set(declarations)
    mathlib = json.loads((ROOT/'validation/mathlib.json').read_text(encoding='utf-8'))
    assert mathlib['revision']==lean['dependency_revision']==mathlib['installed_revision']
    assert mathlib['project_manifest_sha256']==digest('lean/lake-manifest.json')
    manifest = json.loads((ROOT/'lean/lake-manifest.json').read_text(encoding='utf-8'))
    resolved = {item['name']: item['rev'] for item in manifest['packages']}
    assert resolved['mathlib']==mathlib['revision']
    for package in mathlib['dependency_manifest']['packages']:
        assert resolved[package['name']]==package['rev']
    for name, record in mathlib['files'].items():
        assert digest(record['path'])==record['sha256'], 'Stale cached metadata: '+name
        assert digest('lean/.lake/packages/mathlib/'+name)==record['sha256'], 'Stale installed metadata: '+name
    assert set(mathlib['checked_adapter_declarations']) <= set(declarations)
    assert lean["appendix_multiply_byte_code_checked"]
    assert set(lean["checked_appendix_multiply_byte_code_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_byte_execution_checked"]
    assert set(lean["checked_appendix_multiply_byte_execution_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_refinement_checked"]
    assert set(lean["checked_appendix_multiply_refinement_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_packets_checked"]
    assert set(lean["checked_appendix_multiply_packets_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_image_checked"]
    assert set(lean["checked_appendix_multiply_image_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_packing_checked"]
    assert set(lean["checked_appendix_multiply_packing_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_regions_checked"]
    assert set(lean["checked_appendix_multiply_regions_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_layout_checked"]
    assert set(lean["checked_appendix_multiply_layout_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_data_checked"]
    assert set(lean["checked_appendix_multiply_data_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_linear_checked"]
    assert set(lean["checked_appendix_multiply_linear_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_setup_checked"]
    assert set(lean["checked_appendix_multiply_setup_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_paths_checked"]
    assert set(lean["checked_appendix_multiply_paths_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_byte_blocks_checked"]
    assert set(lean["checked_appendix_multiply_byte_blocks_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_byte_simulation_checked"]
    assert set(lean["checked_appendix_multiply_byte_simulation_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_byte_loop_checked"]
    assert set(lean["checked_appendix_multiply_byte_loop_declarations"]) <= set(declarations)
    assert lean["appendix_multiply_byte_correct_checked"]
    assert set(lean["checked_appendix_multiply_byte_correct_declarations"]) <= set(declarations)
    assert lean['terminal_marker_checked']
    assert len(lean['checked_terminal_marker_declarations'])==27
    assert set(lean['checked_terminal_marker_declarations'])<=set(declarations)
    assert lean['accumulator_finalization_checked']
    assert len(lean['checked_accumulator_finalization_declarations'])==49
    assert set(lean['checked_accumulator_finalization_declarations'])<=set(declarations)
    assert lean['input_operand_checked']
    assert len(lean['checked_input_operand_declarations'])==15
    assert set(lean['checked_input_operand_declarations'])<=set(declarations)
    assert lean['dword_owner_checked']
    assert len(lean['checked_dword_owner_declarations'])==17
    assert set(lean['checked_dword_owner_declarations'])<=set(declarations)
    assert lean['dword_copy_checked']
    assert len(lean['checked_dword_copy_declarations'])==77
    assert set(lean['checked_dword_copy_declarations'])<=set(declarations)
    ledger = (ROOT/'lean/PROOF_LEDGER.md').read_text(encoding='utf-8')
    obligations = re.findall(r'^\| ([A-Z][0-9]{2,}) \|',ledger,re.M)
    assert len(set(obligations))==len(obligations), 'Duplicate ledger ID'
    print(f"Lean: {len(declarations)} audited declarations; {len(obligations)} unique ledger obligations; source hashes match")
    appendix = json.loads((ROOT/'validation/appendix-calls.json').read_text(encoding='utf-8'))
    assert appendix['passed'] and appendix['architecture']=='x86' and len(appendix['cases'])==3
    for name, expected in appendix['sources'].items():
        assert digest(name)==expected, 'Stale appendix CALL source: '+name
    for name, expected in appendix['artifacts'].items():
        assert digest(name)==expected, 'Stale appendix CALL artifact: '+name
    assert [case['form'] for case in appendix['cases']]==['callRelative','callRelative','callIndirect']
    assert [case['payload_offset'] for case in appendix['cases']]==[1,1,2]
    assert [case['bytes'] for case in appendix['cases']]==['e800000000','e800000000','ff1505000000']
    print('Appendix CALL typing: source/artifact hashes and three MASM comparators match')
    branch = json.loads((ROOT/'validation/branch.json').read_text(encoding='utf-8'))
    assert branch['passed'] and branch['architecture']=='x86' and branch['cases']==74400
    assert branch['lean_audit_sha256']==digest('validation/lean.json'), 'Stale branch proof provenance'
    for name,expected in branch['sources'].items():
        assert digest(name)==expected, 'Stale branch source: '+name
    for name,expected in branch['artifacts'].items():
        assert digest(name)==expected, 'Stale branch artifact: '+name
    assert len(branch['runs'])==len(branch['assembler'])==len(branch['lean_layouts'])==len(branch['lean_spaced'])==12 and len(branch['lean_shapes'])==13
    expected_names = ['Branch'+mode+relation for mode in ['U','S'] for relation in ['lt','le','eq','ne','gt','ge']]
    assert [item['name'] for item in branch['runs']]==[item['name'] for item in branch['assembler']]==expected_names
    assert sum(item['cases'] for item in branch['runs'])==74400
    assert sum(item['instruction_headers'] for item in branch['assembler'])==338
    assert sum(item['owner_fields'] for item in branch['assembler'])==84
    assert sum(item['checked_relocations'] for item in branch['assembler'])==338
    assert json.loads((ROOT/'validation/.build/branch/layouts.json').read_text(encoding='utf-8'))==branch['lean_layouts']
    assert json.loads((ROOT/'validation/.build/branch/spaced.json').read_text(encoding='utf-8'))==branch['lean_spaced']
    assert json.loads((ROOT/'validation/.build/branch/sites.json').read_text(encoding='utf-8'))==[item['sites'] for item in branch['lean_spaced']]
    for run,layout,reference,spaced in zip(branch['runs'],branch['assembler'],branch['lean_layouts'],branch['lean_spaced']):
        assert run['passed'] and run['cases']==run['taken']+run['fallthrough']==6200
        assert run['taken']>0 and run['fallthrough']>0
        assert layout['tail_bytes']==11 and layout['continuation_bytes']==30
        assert layout['prefix_instructions'] in range(10,18)
        assert len(layout['lean_shape_names'])==layout['instruction_headers']
        assert layout['lean_prefix_checked'] and layout['lean_prefix_packets']==len(reference['prefix'])==layout['prefix_instructions']
        assert (layout['signed'],layout['relation'])==(reference['signed'],reference['relation'])
        assert layout['prefix_bytes']==reference['prefix_bytes']
        assert layout['lean_own_offsets']==reference['field_offsets']
        assert spaced['valid'] and spaced['fields']==layout['fields']
        assert layout['lean_spaced_checked'] and layout['lean_spaced_packets']==len(spaced['packets'])==layout['instruction_headers']
        assert layout['spaced_sites']==spaced['sites'] and layout['spaced_gaps']==spaced['gaps']
        assert all(gap>=0 for gap in spaced['gaps'])
        assert spaced['fall']==layout['fall_entry'] and spaced['sites']['taken']==layout['taken_entry']
        assert spaced['delta']==layout['relocation_delta']
    assert {name for layout in branch['assembler'] for name in layout['lean_shape_names']}=={shape['name'] for shape in branch['lean_shapes']}
    assert sum(item['lean_prefix_packets'] for item in branch['assembler'])==158
    assert sum(item['lean_spaced_packets'] for item in branch['assembler'])==338
    print('Whole x86 branch: 74400 cases; 12 layouts/338 headers/84 fields; all 338 complete pure packets match the spaced Lean emitter')
    assert lean['appendix_branch_geometry_checked']
    assert len(lean['checked_appendix_branch_geometry_declarations'])==15
    assert set(lean['checked_appendix_branch_geometry_declarations'])<=set(declarations)
    geometry=json.loads((ROOT/'validation/branch_geometries.json').read_text(encoding='utf-8'))
    assert geometry['passed'] and geometry['architecture']=='x86'
    assert geometry['region_orders']==24 and geometry['relation_modes']==12
    assert geometry['layouts']==288 and geometry['backward_layouts']==144 and geometry['executions']==1785600
    assert geometry['pure_packets']==8112 and geometry['owner_fields']==2016 and geometry['address_relocations']==8112
    assert geometry['original_pure_instruction_order'] and geometry['current_byte_whole_execution_proof'] and geometry['ten_static_checks']
    assert geometry['proofs']==lean['checked_appendix_branch_geometry_declarations']
    assert geometry['lean_audit_sha256']==digest('validation/lean.json')
    assert len(geometry['batches'])==24 and len({tuple(b['order']) for b in geometry['batches']})==24
    assert all(set(b['order'])=={'stack','core','taken','data'} and b['executions']==74400 and len(b['cases'])==12 for b in geometry['batches'])
    assert all(c['executions']==6200 and c['taken']+c['fallthrough']==6200 and c['taken']>0 and c['fallthrough']>0 for b in geometry['batches'] for c in b['cases'])
    for category in ['sources','artifacts']:
        for name,expected in geometry[category].items():assert digest(name)==expected,'Stale branch geometry '+category+': '+name
    print('Arbitrary disjoint branch geometry: universal original-image trace/target/register/CF/owned-write/exact byte frame; 24 physical orders/288 layouts/144 backward targets/1785600 native executions/8112 full packets/2016 owner fields')
    for record in ['baseline.json','baseline-after-repair.json','defaddr.json','pure.json']:
        evidence = json.loads((ROOT/'validation'/record).read_text(encoding='utf-8'))
        for name,expected in evidence['sources'].items():
            assert digest(name)==expected, 'Stale '+record+' source: '+name
        assert evidence['runs'], record
        print(record+': source hashes match; '+str(len(evidence['runs']))+' recorded runs')
    pure = json.loads((ROOT/'validation/pure.json').read_text(encoding='utf-8'))
    assert 'validation/run_defaddr.py' in pure['sources'], 'Missing shared launcher provenance'
    assert pure['lean_audit_sha256']==digest('validation/lean.json'), 'Stale native proof provenance'
    assert pure['lean_source_hashes']==lean['sources'], 'Native/Lean source mismatch'
    assert {run['architecture'] for run in pure['runs']}=={'x86','x64'}
    for run in pure['runs']:
        assert run['passed'] and run['cases']==len(run['scenarios'])
        assert run['closed_loop_cases']==run['terminal_cases']
    encoding = json.loads((ROOT/'validation/encoding.json').read_text(encoding='utf-8'))
    assert encoding['passed'] and encoding['toolchain']==lean['toolchain']
    assert encoding['lean_audit_sha256']==digest('validation/lean.json'), 'Stale encoding proof provenance'
    assert encoding['native_report_sha256']==digest('validation/pure.json'), 'Stale encoding fixture provenance'
    assert len(encoding['shapes'])==26
    for name,expected in encoding['sources'].items():
        assert digest(name)==expected, 'Stale encoding source: '+name
    assert {str(path.relative_to(ROOT)) for path in (project/'SmcTuring/Native').glob('*.lean')} <= set(encoding['sources'])
    assert {run['architecture'] for run in encoding['runs']}=={'x86','x64'}
    for run in encoding['runs']:
        assert run['passed'] and run['instruction_headers']>0 and run['owned_fields']==8243
        assert run['computed_layout_checked']
        assert run['host_endpoint_checked']
        assert 0 <= run['computed_layout']['terminal_offset'] < run['computed_layout']['host_span']
        assert len(run['computed_layout']['source_positions'])==64
        assert len(run['computed_layout']['readers'])==23 and len(run['computed_layout']['fields'])==13
        for name,expected in run['artifacts'].items():
            assert digest(name)==expected, 'Stale encoding artifact: '+name
        print(f"{run['architecture']}: encoding/relocation evidence matches {run['instruction_headers']} headers and {run['owned_fields']} fields")
    manuals = json.loads((ROOT/'validation/intel-manuals.json').read_text())
    assert set(manuals)=={'vol2a','vol2b','vol2d','vol3a'}, 'Selected ISA reference inventory changed'
    for name, record in manuals.items():
        path = 'validation/.cache/intel-093/'+name+'.pdf'
        assert 'sha256' in record, 'Manual download failed: '+name
        if (ROOT/path).is_file(): assert digest(path)==record['sha256']
    print('Native proof provenance and cached primary-manual hashes match')
    half = json.loads((ROOT/'validation/half-frame.json').read_text(encoding='utf-8'))
    assert half['passed'] and half['lean_audit_sha256']==digest('validation/lean.json')
    assert half['proofs']==lean['checked_x64_half_frame_declarations']
    for name,expected in half['sources'].items():
        assert digest(name)==expected, 'Stale half-frame source: '+name
    assert {run['architecture'] for run in half['runs']}=={'x86','x64'}
    for run in half['runs']:
        assert run['passed'] and run['cases']==17290 and run['operations']==5 and run['incoming_carry_cases']==2
        for name,expected in run['artifacts'].items():
            assert digest(name)==expected, 'Stale half-frame artifact: '+name
    print('Literal split-word frames: 28 audited proofs; x86/x64 each 17290 cases; source/low AX/CF/full non-target code-byte frame')
    multiply = json.loads((ROOT/'validation/multiplication.json').read_text(encoding='utf-8'))
    assert multiply['passed'] and multiply['architecture']=='x86' and multiply['cases']==11458
    assert multiply['operand_words']==14 and multiply['incoming_carry_cases']==2
    assert multiply['lean_audit_sha256']==digest('validation/lean.json'), 'Stale multiplication proof provenance'
    assert len(multiply['proofs'])==329 and set(multiply['proofs'])<=set(declarations)
    assert multiply['whole_byte_correctness_checked'] and multiply['byte_scratch_fields']==10
    assert multiply['byte_correctness_theorem']=='SmcTuring.Appendix.MultiplyByteCorrect.correct'
    assert multiply['byte_correctness_theorem'] in declarations
    geometry=multiply['geometry']
    assert geometry['lean_geometry_checked'] and geometry['pure_bytes']==382 and geometry['instruction_headers']==55
    assert geometry['delta']==171 and geometry['back_delta']==4294967019
    packets=multiply['packets']
    assert packets['complete_packets_checked'] and packets['executed_packets']==55 and packets['inactive_owner_packets']==4
    assert packets['compared_bytes']==422 and packets['address_relocations']==57 and packets['operand_fields']==14
    assert packets['image_owners_checked'] and packets['initial_image_packets']==59 and packets['mutable_image_fields']==14
    for category in ['sources','artifacts']:
        for name,expected in multiply[category].items():
            assert digest(name)==expected, 'Stale multiplication '+category+': '+name
    print('Literal Listing 11 multiplication: 329 audited multiplication proofs; 11458 x86 cases; 14 fields/GPRs/ESP/CF/exterior byte frame/repeated calls; Lean geometry/59 complete packets/57 address relocations/14 image owner windows')
    constant = json.loads((ROOT/'validation/constant.json').read_text(encoding='utf-8'))
    assert constant['passed'] and constant['complete_packets_checked'] and constant['architecture']=='x86'
    assert constant['lean_audit_sha256']==digest('validation/lean.json'), 'Stale constant-emitter proof provenance'
    assert len(constant['proofs'])==184
    assert constant['word_proofs']==lean['checked_appendix_constant_word_declarations']
    assert constant['byte_proofs']==lean['checked_appendix_constant_byte_declarations']
    assert lean['appendix_constant_geometry_checked']
    assert constant['geometry_proofs']==lean['checked_appendix_constant_geometry_declarations']
    # Declaration print order within a module can differ from the named group
    # order; require the same complete, duplicate-free theorem inventory.
    assert len(constant['proofs'])==len(set(constant['proofs']))
    assert set(constant['proofs'])==set(constant['word_proofs']+constant['byte_proofs']+constant['geometry_proofs'])
    assert constant['actual_lean_codec_checked'] and constant['static_byte_trace_checked']
    assert constant['byte_trace_theorem']=='SmcTuring.Appendix.ConstantSimulation.original_image_correct'
    assert constant['byte_trace_theorem'] in declarations
    assert constant['variable_emitter_layout_derived'] and constant['complete_geometry_codec_checked']
    assert constant['emitter_correct_theorem']=='SmcTuring.Appendix.ConstantCorrect.correct'
    assert constant['reusable_trace_theorem']=='SmcTuring.Appendix.ConstantCorrect.reusable_trace'
    assert constant['reusable_correct_theorem']=='SmcTuring.Appendix.ConstantCorrect.reusable_correct'
    assert {constant['emitter_correct_theorem'],constant['reusable_trace_theorem'],constant['reusable_correct_theorem']} <= set(declarations)
    assert constant['constants']>=600 and constant['cases']==constant['constants']*82
    assert constant['pure_packets']>10000 and constant['compared_bytes']>70000
    assert constant['baseline']['source_sha256']==digest('validation/.cache/morse-2018.pdf')
    for category in ['sources','artifacts']:
        for name,expected in constant[category].items():
            assert digest(name)==expected, 'Stale constant-emitter '+category+': '+name
    print('Listing 6: 184 audited positive word/codec/refinement/image/emitter geometry/live-trace proofs; complete original-image contract and reusable current-byte fetch derived; finite native product/scratch/GPRs/ESP/CF/exterior-byte/reuse and complete actual Lean-coded packets pass')
    zero = json.loads((ROOT/'validation/zero.json').read_text(encoding='utf-8'))
    assert lean['appendix_zero_checked'] and zero['passed'] and zero['actual_lean_codec_checked']
    assert zero['lean_audit_sha256']==digest('validation/lean.json')
    assert zero['proofs']==lean['checked_appendix_zero_declarations'] and len(zero['proofs'])==18
    assert set(zero['proofs']) <= set(declarations)
    assert zero['corrected_theorem']=='SmcTuring.Appendix.ZeroImage.correct'
    assert zero['original_image_theorem']=='SmcTuring.Appendix.ZeroImage.original_image_correct'
    for name,expected in zero['sources'].items():assert digest(name)==expected,'Stale DEFZERO source: '+name
    assert [r['architecture'] for r in zero['runs']]==['x86','x64']
    for run in zero['runs']:
        assert run['passed'] and run['executions']==9312 and run['live_words']==582
        assert run['baseline']['field_before']==run['baseline']['field_after']!=0
        assert run['baseline']['immediate_bytes']==1 and run['baseline']['typed_literal_opcode']==0x83
        assert run['corrected_immediate_bytes']==4 and run['own_field_offset']==6
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale DEFZERO artifact: '+name
    print('DEFZERO: 18 audited positive current-byte proofs; x86/x64 each 9312 executions; complete forced imm32 packets/owned DWORD/zero/register/CF/exterior-byte/reuse checks')
    conversion = json.loads((ROOT/'validation/conversion.json').read_text(encoding='utf-8'))
    assert lean['native_conversion_checked'] and conversion['passed'] and conversion['actual_lean_codec_checked']
    assert conversion['admissible_geometry_checked'] and conversion['owner_packets_codec_checked']
    assert conversion['lean_audit_sha256']==digest('validation/lean.json')
    assert conversion['proofs']==lean['checked_native_conversion_declarations'] and len(conversion['proofs'])==53
    assert set(conversion['proofs'])<=set(declarations)
    assert conversion['corrected_theorem']=='SmcTuring.Native.ConversionImage.correct'
    assert conversion['original_image_theorem']=='SmcTuring.Native.ConversionImage.original_image_correct'
    for name,expected in conversion['sources'].items():assert digest(name)==expected,'Stale conversion source: '+name
    assert [r['architecture'] for r in conversion['runs']]==['x86','x64']
    for run in conversion['runs']:
        assert run['passed'] and run['executions']==run['live_words']*48 and run['live_words']>=440
        assert run['layouts']==6 and run['complete_helper_packets']==18 and run['complete_owner_packets']==8
        assert run['complete_helper_bytes']==(102 if run['architecture']=='x86' else 126)
        assert run['complete_owner_bytes']==(40 if run['architecture']=='x86' else 80)
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale conversion artifact: '+name
    print('Listing 6 conversion: 53 positive x86/x64 current-byte proofs; six native layouts per architecture; all GPRs/SP/CF/source/destination/exterior bytes/reuse; 18 complete helper and 8 code-owner packets per architecture match actual Lean codec')
    template = json.loads((ROOT/'validation/template.json').read_text(encoding='utf-8'))
    assert template['passed'] and lean['native_template_copy_checked']
    assert template['lean_audit_sha256']==digest('validation/lean.json')
    assert template['proofs']==lean['checked_native_template_copy_declarations'] and len(template['proofs'])==41
    assert set(template['proofs'])<=set(declarations)
    assert template['actual_lean_codec_checked'] and template['compilation_bindings_checked'] and template['whole_template_fetch_checked'] and template['original_image_construction_checked']
    assert template['original_image_theorem']=='SmcTuring.Native.TemplateCopy.original_image_correct'
    assert template['whole_address_theorem']=='SmcTuring.Native.TemplateCopy.original_addresses_correct'
    assert template['copy_theorem']=='SmcTuring.Native.TemplateCopy.correct'
    assert template['memory_target_theorem']=='SmcTuring.Native.TemplateRelocation.memory_target'
    assert template['call_target_theorem']=='SmcTuring.Native.TemplateRelocation.call_target'
    assert template['moffs_payload_theorem']=='SmcTuring.Native.TemplateCopy.moffs_payload'
    for name,expected in template['sources'].items():assert digest(name)==expected,'Stale template source: '+name
    assert [r['architecture'] for r in template['runs']]==['x86','x64']
    for run in template['runs']:
        assert run['passed'] and run['executions']==768 and run['layouts']==run['complete_templates']==4
        assert run['compared_template_bytes']==(332 if run['architecture']=='x86' else 412)
        assert run['instruction_headers']==60 and run['all_memory_operations']==10
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale template artifact: '+name
    print('Complete compile-bound template copy: 41 audited proofs; constructed original images/full TRANSFERDATA trace/every copied packet fetch; internal/external MOFFS/all memory operations/RIP/CALL addresses; x86/x64 each 768 executions/4 independent forward-backward layouts/60 complete destination packets match Lean')
    transfer = json.loads((ROOT/'validation/transfer.json').read_text(encoding='utf-8'))
    assert lean['native_string_copy_checked'] and transfer['passed'] and transfer['actual_lean_codec_checked'] and transfer['complete_macro_packets_checked']
    assert transfer['lean_audit_sha256']==digest('validation/lean.json')
    assert transfer['proofs']==lean['checked_native_string_copy_declarations'] and len(transfer['proofs'])==51
    assert set(transfer['proofs'])<=set(declarations)
    assert lean['native_string_execution_checked'] and transfer['selected_body_current_fetch_checked'] and transfer['live_macro_decoding_checked']
    assert transfer['execution_proofs']==lean['checked_native_string_execution_declarations'] and len(transfer['execution_proofs'])==54
    assert set(transfer['execution_proofs'])<=set(declarations)
    assert lean['native_string_stages_checked'] and transfer['initializer_trace_checked'] and transfer['prefix_trace_checked'] and transfer['restoration_pairs_checked'] and transfer['actual_program_encoding_checked']
    assert transfer['stage_proofs']==lean['checked_native_string_stage_declarations'] and len(transfer['stage_proofs'])==50
    assert set(transfer['stage_proofs'])<=set(declarations)
    assert lean['native_string_macro_checked'] and transfer['continuous_macro_trace_checked'] and transfer['complete_final_state_checked'] and transfer['static_macro_resources_checked']
    assert transfer['macro_proofs']==lean['checked_native_string_macro_declarations'] and len(transfer['macro_proofs'])==46
    assert set(transfer['macro_proofs'])<=set(declarations)
    assert transfer['macro_trace_theorem']=='SmcTuring.Native.StringMacroTrace.correct'
    assert transfer['macro_effect_theorem']=='SmcTuring.Native.StringMacroTrace.run_correct'
    assert transfer['macro_reuse_theorem']=='SmcTuring.Native.StringMacroTrace.reusable'
    assert transfer['macro_range_theorem']=='SmcTuring.Native.StringMacroLayout.tail_ranges'
    assert transfer['prefix_theorem']=='SmcTuring.Native.StringSetupTrace.initialized_trace'
    assert transfer['prefix_effect_theorem']=='SmcTuring.Native.StringSetup.effect'
    assert transfer['restoration_theorem']=='SmcTuring.Native.StringRestore.trace'
    assert transfer['program_encoding_theorem']=='SmcTuring.Native.StringProgram.encoding'
    assert transfer['body_theorem']=='SmcTuring.Native.StringMoveTrace.correct'
    assert transfer['copied_packet_theorem']=='SmcTuring.Native.StringTemplate.copied_fetch'
    assert transfer['rip_relocation_theorem']=='SmcTuring.Native.StringTemplate.rip_target'
    assert transfer['byte_copy_theorem']=='SmcTuring.Native.StringPlan.correct'
    assert transfer['cursor_theorem']=='SmcTuring.Native.StringCursor.pair_correct'
    assert transfer['memory_theorem']=='SmcTuring.Native.StringFields.effect'
    for name,expected in transfer['sources'].items():assert digest(name)==expected,'Stale TRANSFERDATA source: '+name
    assert [r['architecture'] for r in transfer['runs']]==['x86','x64']
    for run in transfer['runs']:
        assert run['passed'] and run['executions']==6144 and run['sizes']==run['complete_macros']==48 and run['cursor_fields']==96
        assert run['instruction_headers']==(1292 if run['architecture']=='x86' else 1160)
        assert run['compared_bytes']==(3762 if run['architecture']=='x86' else 5682)
        assert run['baseline']['typed_literal'] and run['baseline']['intended_buffers_unchanged'] and run['baseline']['copied_other_buffer']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale TRANSFERDATA artifact: '+name
    print('Listing 5 TRANSFERDATA: 51 positive byte/plan/cursor/unified-memory/codec proofs plus 54 selected current-byte body/template and 50 initializer/prefix/restoration/program proofs plus 46 continuous whole-macro original-image/full-state/reuse proofs; live classifier/fetch decodes complete macros; x86/x64 each 6144 executions; 48 complete macros and 96 cursor fields per architecture match Lean; complete buffers/SI/DI/GPRs/SP/CF/code frame/reuse checks')
    assert lean['division_foundation_checked']
    assert len(lean['checked_division_foundation_declarations'])==17
    assert set(lean['checked_division_foundation_declarations'])<=set(declarations)
    print('Listing 12 division foundations: 9 arithmetic and 8 positive minimal field/guard/continuation/CALL repair proofs; full literal execution is checked separately below')
    assert lean['division_data_checked']
    assert len(lean['checked_division_data_declarations'])==117
    assert set(lean['checked_division_data_declarations'])<=set(declarations)
    print('Listing 12 signed algebra and literal initialization/32-pass body/result data execution: 117 checked declarations; original-image current-byte execution is checked separately below')
    assert lean['division_control_checked']
    assert len(lean['checked_division_control_declarations'])==50
    assert set(lean['checked_division_control_declarations'])<=set(declarations)
    print('Listing 12 word/control: 50 checked guard, CALL/stack/block/PC, counter-schedule/terminal observation proofs; initialized bootstrap derives the final packed invariant and reusable stack')
    for group,count in [('division_complete_word',16),('division_byte_primitives',40),('division_refinement',17),('division_image',15),('division_packets',10),('division_byte_execution',170)]:
        assert lean[group+'_checked']
        assert len(lean['checked_'+group+'_declarations'])==count
        assert set(lean['checked_'+group+'_declarations'])<=set(declarations)
    print('Listing 12 complete word/control: 16 original-input/result/signed-integer/CF/stack/register/frame/purity proofs; 40 exact byte primitive, 17 data effect refinement, 15 mutable image and 10 literal packet proofs')
    division = json.loads((ROOT/'validation/division.json').read_text(encoding='utf-8'))
    assert division['passed'] and division['architecture']=='x86' and division['executions']==52648
    assert division['foundation_proofs']==lean['checked_division_foundation_declarations']
    assert division['data_proofs']==lean['checked_division_data_declarations']
    assert division['literal_word_data_execution_proof']
    assert division['control_proofs']==lean['checked_division_control_declarations']
    assert division['actual_lean_control_geometry_checked']
    geometry=division['geometry']
    assert geometry['modes']==4 and geometry['data_instruction_lengths']==247
    assert geometry['direct_calls']==12 and geometry['pure_bytes']==2402
    assert not geometry['complete_packet_comparison']
    assert [row['end']-row['origin'] for row in geometry['references']]==[464,464,756,718]
    assert all(row['delta']==218 and row['back_delta']==4294966972 for row in geometry['references'])
    assert division['lean_audit_sha256']==digest('validation/lean.json')
    assert division['original_instruction_order'] and division['unsigned_nonzero']
    assert division['signed_truncation']=='toward zero'
    assert division['signed_quotient_overflow']=='MIN_INT/-1 excluded'
    assert division['signed_remainder_overflow_case']=='included: zero remainder'
    assert division['full_gpr_stack_input_reuse_code_frame_checked']
    assert division['complete_lean_packet_comparison'] and division['whole_literal_execution_proof']
    assert division['whole_word_control_execution_proof'] and division['original_input_result_frame_purity_proof']
    for group,key in [('division_complete_word','complete_word_proofs'),('division_byte_primitives','byte_primitive_proofs'),('division_refinement','refinement_proofs'),('division_image','image_proofs'),('division_packets','packet_proofs'),('division_byte_execution','byte_execution_proofs')]:
        assert division[key]==lean['checked_'+group+'_declarations']
    packets=division['packets']
    assert packets['complete_packets'] and packets['complete_owner_fields'] and not packets['whole_current_byte_execution']
    assert packets['constructed_original_image_checked'] and packets['admissible_geometry_checked']
    assert all(all(row['admissible']) for row in packets['references'])
    assert packets['modes']==4 and packets['pure_packets']==331 and packets['unique_packets']==344
    assert packets['compared_bytes']==2532 and packets['address_relocations']==333 and packets['mode_owned_fields']==91
    assert [r['executions'] for r in division['runs']]==[13168,13168,13144,13168]
    assert [r['fields'] for r in division['runs']]==[19,19,27,26]
    for category in ['sources','artifacts']:
        for name,expected in division[category].items():assert digest(name)==expected,'Stale division '+category+': '+name
    print('Listing 12 corrected x86: 52648 executions in all four unsigned/signed quotient/remainder modes; input/GPR/ESP/CF/exterior-code/reuse frames; 344 complete packets/2532 bytes/333 DIR32 sites/91 mode-owned fields match actual Lean; 170 universal original-image current-byte execution proofs construct all four results/registers/stack/CF/PC, code-write purity, exact exterior-byte frame and maintained-image reuse; physical ISA/fetch remains E05/A01')
    terminal = json.loads((ROOT/'validation/terminal.json').read_text(encoding='utf-8'))
    assert terminal['passed'] and terminal['actual_lean_codec_checked'] and terminal['complete_object_and_loaded_packets_checked']
    assert terminal['lean_audit_sha256']==digest('validation/lean.json')
    assert terminal['proofs']==lean['checked_terminal_marker_declarations']
    assert terminal['theorem']=='SmcTuring.Native.TerminalMarker.correct'
    assert terminal['purity_theorem']=='SmcTuring.Native.TerminalMarker.pure'
    assert [run['architecture'] for run in terminal['runs']]==['x86','x64']
    for run in terminal['runs']:
        assert run['passed'] and run['typed_original_executions']==run['corrected_executions']==4128
        assert run['own_immediate_offset']==6 and run['instruction_bytes']==10
        assert run['full_packets']==run['code_address_relocations']==2
        assert run['all_gpr_stack_status_flags_endpoint_frame_reuse']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale terminal artifact: '+name
    for name,expected in terminal['sources'].items():assert digest(name)==expected,'Stale terminal source: '+name
    print('Listing 2 terminal: 27 positive both-mode current-byte/PC/register/purity/output/reuse proofs; x86/x64 each 4128 typed-original and 4128 corrected native cases; complete loaded/object packets and DIR32/REL32_4 symbol/addend matches')
    accumulator = json.loads((ROOT/'validation/accumulator.json').read_text(encoding='utf-8'))
    assert accumulator['passed'] and accumulator['actual_lean_codec_checked'] and accumulator['complete_loaded_and_object_packets_checked']
    assert accumulator['lean_audit_sha256']==digest('validation/lean.json')
    assert accumulator['proofs']==lean['checked_accumulator_finalization_declarations']
    assert accumulator['theorem']=='SmcTuring.Native.AccumulatorFinalization.surround'
    assert accumulator['purity_theorem']=='SmcTuring.Native.AccumulatorFinalization.surrounding_pure'
    assert [run['architecture'] for run in accumulator['runs']]==['x86','x64']
    for run in accumulator['runs']:
        assert run['passed'] and run['executions']==38400 and run['layouts']==6
        assert run['control_packets']==48 and run['owner_packets']==24 and run['address_relocations']==54
        assert run['compared_bytes']==(408 if run['architecture']=='x86' else 594)
        assert run['full_gpr_stack_status_flags_outputs_endpoint_code_frame_reuse']
        assert run['original_listing9_instruction_order'] and run['complete_word_fields']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale accumulator artifact: '+name
    for name,expected in accumulator['sources'].items():assert digest(name)==expected,'Stale accumulator source: '+name
    print('Listing 9/full-width finalization: 49 positive original-order layout/effect/live-image/original-pointer/body/terminal/purity/reuse/output proofs; x86/x64 each 38400 executions/six owner orders/72 loaded and COFF packets/54 relocations match Lean; exact AX/GPR/SP/flags/body-result/reserved-reset/exterior-byte/reentry frames')
    input_operand = json.loads((ROOT/'validation/input_operand.json').read_text(encoding='utf-8'))
    assert input_operand['passed'] and input_operand['actual_lean_codec_checked'] and input_operand['complete_loaded_and_object_packets_checked']
    assert input_operand['lean_audit_sha256']==digest('validation/lean.json')
    assert input_operand['proofs']==lean['checked_input_operand_declarations']
    assert input_operand['dword_execution_checked'] and input_operand['dword_proofs']==lean['checked_dword_copy_declarations']
    assert input_operand['dword_theorem']=='SmcTuring.Appendix.InputDword.copy_correct'
    assert input_operand['dword_purity_theorem']=='SmcTuring.Appendix.InputDword.copy_pure'
    assert input_operand['theorem']=='SmcTuring.Appendix.InputOperand.copy_correct'
    assert input_operand['purity_theorem']=='SmcTuring.Appendix.InputOperand.copy_pure'
    assert [run['architecture'] for run in input_operand['runs']]==['x86','x64']
    for run in input_operand['runs']:
        assert run['passed'] and run['typed_original_executions']==run['corrected_executions']==6400
        assert run['source_offset']==6 and run['target_offset']==3
        assert run['complete_packets']==12 and run['address_relocations']==10 and run['admissible_checks']==9
        if run['architecture']=='x64':assert run['actual_natural_addresses_above_dword']
        assert run['compared_bytes']==(88 if run['architecture']=='x86' else 90)
        assert run['current_symbol_low_ax_zero_extension_gpr_stack_flags_endpoint_exterior_reuse']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale input-operand artifact: '+name
    for name,expected in input_operand['sources'].items():assert digest(name)==expected,'Stale input-operand source: '+name
    print('Listing 8 input operand: 15 local plus 77 universal both-mode DWORD codec/layout/effect/current-image/source/target/purity/frame proofs; x86/x64 each 6400 corrected and 6400 typed-original cases/12 complete loaded and COFF packets/10 relocations/nine static checks match Lean; actual x64 addresses above 4GiB and proper RAX zero extension checked')
    dword_owner = json.loads((ROOT/'validation/dword_owner.json').read_text(encoding='utf-8'))
    assert dword_owner['passed'] and dword_owner['actual_lean_codec_checked'] and dword_owner['complete_loaded_and_object_packets_checked']
    assert dword_owner['lean_audit_sha256']==digest('validation/lean.json')
    assert dword_owner['proofs']==lean['checked_dword_owner_declarations']
    assert dword_owner['theorem']=='SmcTuring.Native.DwordOwner.correct' and dword_owner['purity_theorem']=='SmcTuring.Native.DwordOwner.pure'
    assert [run['architecture'] for run in dword_owner['runs']]==['x86','x64']
    for run in dword_owner['runs']:
        assert run['passed'] and run['executions']==6400 and run['live_words']==run['complete_live_packets']==40
        assert run['initial_packet']==1 and run['compared_bytes']==410 and run['address_relocations']==1
        assert run['own_immediate_offset']==6 and run['operand_width']==4 and run['instruction_bytes']==10
        assert run['full_ax_gpr_stack_flags_endpoint_live_symbol_whole_packet_reuse']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale DWORD owner artifact: '+name
    for name,expected in dword_owner['sources'].items():assert digest(name)==expected,'Stale DWORD owner source: '+name
    print('Listing 8 DWORD scalar: 17 positive both-mode live/current-byte/patch/zero/purity/full-AX/SP/CF/whole-memory/reuse proofs; each native mode 6400 cases/40 live and one initial complete packet/one COFF relocation match actual Lean')
    for group in ['dword_arithmetic','dword_comparison','input_selection']:
        assert lean[group+'_checked']
        assert set(lean['checked_'+group+'_declarations']) <= set(declarations)
    dword_comparison = json.loads((ROOT/'validation/dword_comparison.json').read_text(encoding='utf-8'))
    assert dword_comparison['passed'] and dword_comparison['actual_lean_codec_checked'] and dword_comparison['complete_loaded_and_object_packets_checked']
    assert dword_comparison['lean_audit_sha256']==digest('validation/lean.json')
    assert dword_comparison['proofs']==lean['checked_dword_comparison_declarations']
    assert dword_comparison['arithmetic_proofs']==lean['checked_dword_arithmetic_declarations']
    assert dword_comparison['theorem']=='SmcTuring.Appendix.DwordComparison.correct'
    assert dword_comparison['purity_theorem']=='SmcTuring.Appendix.DwordComparison.pure'
    assert [run['architecture'] for run in dword_comparison['runs']]==['x86','x64']
    for run in dword_comparison['runs']:
        assert run['passed'] and run['executions']==51200 and run['matches']==1280
        assert run['current_symbols']==40 and run['complete_code_images']==41 and run['owner_packets']==2
        assert run['compared_bytes']==1619 and run['address_relocations']==7 and run['static_checks']==11
        if run['architecture']=='x64':assert run['x64_addresses_above_4GiB']
        assert run['full_ax_gpr_stack_flags_endpoint_scalar_mask_code_frame_reuse']
        for name,expected in run['artifacts'].items():assert digest(name)==expected,'Stale DWORD comparison artifact: '+name
    for name,expected in dword_comparison['sources'].items():assert digest(name)==expected,'Stale DWORD comparison source: '+name
    print('Listing 8 comparison forms: 19 arithmetic/24 packed comparison/10 selection proofs; both modes each 51200 cases/1280 matches/41 complete images/two owners/1619 bytes/seven COFF relocations/11 proved checks; full AX/GPR/SP/status flags/PC/scalar/mask/code-frame/reuse; actual x64 addresses above 4GiB. Interleaved input-copy/scalar-owner and cursor-exchange composition remain separate.')
    from audit_cursor import main as audit_cursor
    from audit_input_update import main as audit_input_update
    audit_cursor()
    audit_input_update()
    for stem in ['cursor','input_update']:
        local=json.loads((ROOT/('validation/'+stem+'_lean.json')).read_text(encoding='utf-8'))
        assert {entry['name'] for entry in local['declarations']} <= set(declarations)
        for name, expected in local['sources'].items():
            if name in lean['sources']:assert lean['sources'][name]==expected,'Local/main proof snapshot mismatch: '+name
    print('Cursor and full input update: 101 standard-axiom declarations and 819200 native cases with fresh artifact/resource evidence.')
    errata = json.loads((ROOT/'validation/errata.json').read_text(encoding='utf-8'))
    assert errata['source_excerpts_checked']==55 and errata['pages']==2
    assert len(errata['positive_proofs'])==121 and set(errata['positive_proofs']) <= set(declarations)
    assert errata['dword_owner_checked']
    assert errata['dword_owner_evidence_sha256']==digest('validation/dword_owner.json')
    assert errata['input_operand_checked']
    assert errata['input_operand_evidence_sha256']==digest('validation/input_operand.json')
    assert errata['terminal_marker_checked']
    assert errata['terminal_evidence_sha256']==digest('validation/terminal.json')
    assert errata['division_whole_byte_execution_checked']
    assert len(errata['division_correctness_proofs'])==6
    assert set(errata['division_correctness_proofs'])<=set(division['byte_execution_proofs'])
    assert errata['lean_evidence_sha256']==digest('validation/lean.json'), 'Stale errata proof provenance'
    assert errata['division_evidence_sha256']==digest('validation/division.json'), 'Stale errata division evidence'
    assert errata['source_sha256']==digest('validation/.cache/morse-2018.pdf'), 'Stale errata publication source'
    packets=multiply['packets']
    assert packets['complete_packets_checked'] and packets['executed_packets']==55 and packets['inactive_owner_packets']==4
    assert packets['compared_bytes']==422 and packets['address_relocations']==57 and packets['operand_fields']==14
    assert packets['image_owners_checked'] and packets['initial_image_packets']==59 and packets['mutable_image_fields']==14
    for category in ['sources','artifacts']:
        for name,expected in errata[category].items():
            assert digest(name)==expected, 'Stale errata '+category+': '+name
    print('Publishable errata: 55 exact source excerpts; 121 positive audited proof references; compact two-page PDF')

if __name__=='__main__': main()
