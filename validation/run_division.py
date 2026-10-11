"""Positive native tests of Listing 12 after the minimum M06/M11 corrections.

This report supplies finite native evidence plus the registered local/arithmetic
Lean foundations and constructed word/control execution. Full original-image
Continuous original-image current-byte execution and full result/register/frame/purity are checked; physical ISA/configuration/fetch refinement remains E05/A01.
"""
from pathlib import Path
import hashlib,json,re,shutil,os
from datetime import date
from audit_encoding import coff
from run_branch import code_relocation_targets,encoded_address
from lean_export import lean_command
from generate_division import generate
from run_defaddr import vc_environment,run
ROOT=Path(__file__).resolve().parents[1]
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def check_geometry(folder,lean):
    code,symbols,relocations=coff(folder/'native.obj','x86')
    labels={name:int(value,16) for value,name in re.findall(
        r'(?m)^\s*([0-9A-F]{8})\s+(Div[0-3](?:PureBegin|PureEnd|L7|Body|L19))::\s*$',
        (folder/'native.lst').read_text(encoding='utf-8',errors='replace'))}
    assert len(labels)==20
    origins=[labels[f'Div{mode}PureBegin'] for mode in range(4)]
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    command=lean_command(ROOT/'lean',binary,['--run','ExportDivisionControl.lean']+[str(value) for value in origins])
    refs=json.loads(run(command,ROOT/'lean',export_env))
    assert len(refs)==4
    addresses=sorted(set(int(value,16) for value in re.findall(r'(?m)^\s*([0-9A-F]{8}):',
        (folder/'native.disasm.txt').read_text(encoding='utf-8'))))
    checked=0;pure_bytes=0;data_instructions=0
    for mode,ref in enumerate(refs):
        assert ref['mode']==mode and ref['origin']==origins[mode]
        assert ref['guard_continuation']==labels[f'Div{mode}L7']
        assert ref['body_continuation']==labels[f'Div{mode}Body']
        assert ref['exit_continuation']==labels[f'Div{mode}L19']
        assert ref['end']==labels[f'Div{mode}PureEnd']
        assert ref['guard']==ref['guard_continuation']+30
        assert ref['body']==ref['body_continuation']+30
        assert ref['exit']==ref['exit_continuation']+30
        starts=[ref['origin'],ref['guard'],ref['body'],ref['exit']]
        ends=[ref['guard_continuation']-11,ref['body_continuation']-11,
              ref['exit_continuation']-11,ref['end']]
        for start,end,lengths in zip(starts,ends,ref['data_lengths']):
            actual=[pc for pc in addresses if start<=pc<=end]
            assert actual[0]==start and actual[-1]==end
            assert [second-first for first,second in zip(actual,actual[1:])]==lengths,(mode,start,lengths,actual)
            data_instructions+=len(lengths)
        for continuation,expected in [('guard_continuation',0),('body_continuation',0),
                                      ('exit_continuation',ref['back_delta'])]:
            call=ref[continuation]-5
            assert code[call]==0xe8 and call+1 not in relocations
            assert int.from_bytes(code[call+1:call+5],'little')==expected
            checked+=1
        delta_store=ref['guard']+sum(ref['data_lengths'][1][:5])
        assert code[delta_store:delta_store+2]==bytes.fromhex('c705')
        assert int.from_bytes(code[delta_store+6:delta_store+10],'little')==ref['delta']==218
        assert ref['exit_continuation']-ref['body_continuation']==ref['delta']
        assert (ref['guard_continuation']-ref['exit_continuation'])%(1<<32)==ref['back_delta']
        pure_bytes+=ref['end']-ref['origin']
    assert [ref['end']-ref['origin'] for ref in refs]==[464,464,756,718]
    assert data_instructions==247 and checked==12 and pure_bytes==2402
    (folder/'lean-control.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
    return dict(modes=4,data_instruction_lengths=data_instructions,direct_calls=checked,pure_bytes=pure_bytes,
                complete_packet_comparison=False,references=refs,
                scope='Actual Lean word/control PCs, all data lengths and native E8 operands/delta stores; complete packet comparison and continuous original-image byte execution are separate checked results.')

def check_packets(folder,lean):
    """Compare original emitted packets with an independent Lean codec/placement."""
    code,_,relocations=coff(folder/'native.obj','x86')
    section,targets=code_relocation_targets(folder/'native.obj')
    labels={}
    for line in (folder/'native.lst').read_text(encoding='utf-8',errors='replace').splitlines():
        address=re.match(r'^\s*([0-9A-F]{8})\b',line)
        label=re.search(r'(Div[0-3](?:PureBegin|PureEnd|X|Y|Result|L\d+)|stptr):',line)
        if address and label:labels[label[1]]=int(address[1],16)
    stack=labels['stptr']
    arguments=[]
    for mode in range(4):
        arguments.extend(labels[f'Div{mode}'+role] for role in ['PureBegin','X','Y','Result'])
    arguments.append(stack)
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    command=lean_command(ROOT/'lean',binary,['--run','ExportDivisionPackets.lean']+[str(value) for value in arguments])
    refs=json.loads(run(command,ROOT/'lean',export_env))
    assert len(refs)==4
    unique={};pure_count=0;owner_count=0
    for mode,ref in enumerate(refs):
        assert ref['mode']==mode and ref['origin']==labels[f'Div{mode}PureBegin']
        assert ref['pure_span']==labels[f'Div{mode}PureEnd']-ref['origin']
        assert len(ref['pure'])==[65,65,103,98][mode]
        pure_count+=len(ref['pure'])
        end=ref['origin']
        for packet in ref['pure']:
            assert packet['pc']==end
            end+=len(packet['bytes'])
        assert end==labels[f'Div{mode}PureEnd']
        expected_fields={labels[f'Div{mode}'+role]+6 for role in ['X','Y','Result']}
        expected_fields|={stack+2,stack+6,labels[f'Div{mode}L10']+1}
        expected_fields|={value+6 for name,value in labels.items()
            if re.fullmatch(f'Div{mode}L'+r'\d+',name) and name not in {f'Div{mode}L7',f'Div{mode}L10',f'Div{mode}L19'}}
        assert set(ref['fields'])==expected_fields,(mode,set(ref['fields'])^expected_fields)
        assert len(ref['fields'])==[19,19,27,26][mode]
        all_packets=ref['pure']+ref['inactive']
        for field in ref['fields']:
            owners=[packet for packet in all_packets if field-packet['pc'] in packet['dynamic_offsets']]
            assert len(owners)==1,(mode,field,owners)
            assert owners[0]['pc']<=field and field+4<=owners[0]['pc']+len(owners[0]['bytes'])
            owner_count+=1
        ordered=sorted(ref['fields'])
        assert all(first+4<=second for first,second in zip(ordered,ordered[1:]))
        assert all(ref['admissible']) and len(ref['admissible'])==6
        assert len(ref['original_image'])==len(all_packets)
        assert sorted(ref['original_image_fields'])==sorted(ref['fields'])
        original={packet['pc']:packet for packet in ref['original_image']}
        assert set(original)=={packet['pc'] for packet in all_packets}
        for packet in all_packets:
            actual=original[packet['pc']]
            assert actual['bytes']==packet['bytes'] and actual['address_relocations']==packet['address_relocations']
            wanted=[field for field in ref['fields'] if field-packet['pc'] in packet['dynamic_offsets']]
            assert sorted(actual['owned_fields'])==sorted(wanted),(mode,packet['pc'],actual['owned_fields'],wanted)
        for packet in all_packets:
            pc=packet['pc'];expected=bytearray(packet['bytes']);end=pc+len(expected)
            for site in packet['address_relocations']:
                offset=site-pc
                value=int.from_bytes(expected[offset:offset+4],'little')
                expected[offset:offset+4]=encoded_address(value,site,targets,section)
            assert code[pc:end]==expected,(mode,pc,code[pc:end].hex(),expected.hex())
            actual={site:kind for site,kind in relocations.items() if pc<=site<end}
            assert actual=={site:6 for site in packet['address_relocations']},(mode,pc,actual,packet['address_relocations'])
            if pc in unique:assert unique[pc]==packet
            else:unique[pc]=packet
    ordered=sorted(unique.values(),key=lambda p:p['pc'])
    assert all(a['pc']+len(a['bytes'])<=b['pc'] for a,b in zip(ordered,ordered[1:]))
    compared_bytes=sum(len(packet['bytes']) for packet in ordered)
    compared_relocations=sum(len(packet['address_relocations']) for packet in ordered)
    assert pure_count==331 and len(unique)==344 and compared_bytes==2532 and compared_relocations==333 and owner_count==91
    (folder/'lean-packets.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
    return dict(modes=4,pure_packets=pure_count,unique_packets=len(unique),compared_bytes=compared_bytes,
      address_relocations=compared_relocations,mode_owned_fields=owner_count,complete_packets=True,
      complete_owner_fields=True,constructed_original_image_checked=True,admissible_geometry_checked=True,
      whole_current_byte_execution=False,command=command,references=refs,
      scope='All initial pure and inactive owner packets, exact headers/full operands/sites/ends, DIR32 relocations and full separated owner words match actual Lean. This initial packet comparison supplements the separately checked continuous original-image byte execution.')

def main():
    folder=ROOT/'validation/.build/division';folder.mkdir(parents=True,exist_ok=True)
    (folder/'native.asm').write_text(generate(),encoding='utf-8')
    env=vc_environment('x86')
    def tool(name):
        found=shutil.which(name,path=env['PATH'])
        assert found,name
        return found
    commands=[
      [tool('ml.exe'),'/nologo','/c','/safeseh','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst'),str(folder/'native.asm')],
      [tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/division_native.cpp'),'/Fo'+str(folder/'harness.obj')],
      [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'division.exe'),str(folder/'harness.obj'),str(folder/'native.obj')]]
    for command in commands:print(run(command,folder,env),end='',flush=True)
    output=run([str(folder/'division.exe')],folder,env)
    print(output,end='',flush=True);(folder/'run.log').write_text(output,encoding='utf-8')
    (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
    matches=re.findall(r'Listing 12 mode (\d): PASS (\d+) executions; mod=(\d) sign=(\d); (\d+) complete fields',output)
    assert len(matches)==4
    runs=[dict(mode=int(mode),executions=int(count),mod=bool(int(mod)),signed=bool(int(sign)),fields=int(fields)) for mode,count,mod,sign,fields in matches]
    assert [r['executions'] for r in runs]==[13168,13168,13144,13168]
    lean=json.loads((ROOT/'validation/lean.json').read_text(encoding='utf-8'))
    assert lean['division_foundation_checked'] and lean['division_data_checked'] and lean['division_control_checked']
    assert all(lean[group+'_checked'] for group in ['division_complete_word','division_byte_primitives','division_refinement','division_image','division_packets','division_byte_execution'])
    geometry=check_geometry(folder,lean)
    packets=check_packets(folder,lean)
    print('Listing 12 complete packets: PASS 344 unique packets, 2532 bytes, 333 DIR32 sites, 91 mode-owned fields',flush=True)
    print('Listing 12 control geometry: PASS four modes; 247 data lengths, 12 direct CALL operands, 2402 pure bytes',flush=True)
    sources=(['validation/generate_division.py','validation/division_native.cpp','validation/run_division.py',
      'validation/audit_encoding.py','validation/run_branch.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportDivisionControl.lean','lean/ExportDivisionPackets.lean',
      'lean/SmcTuring/Appendix/DivisionAlgebra.lean','lean/SmcTuring/Appendix/DivisionRepairs.lean'] +
      ['lean/SmcTuring/Appendix/'+module+'.lean' for module in ['DivisionSignedAlgebra', 'DivisionWords', 'DivisionWordAlgebra', 'DivisionPrefixes', 'DivisionBody', 'DivisionStages', 'DivisionPacked', 'DivisionIteration', 'DivisionDataCorrect','DivisionGuard','DivisionControl','DivisionBlocks','DivisionExecution','DivisionObservations','DivisionCorrect','DivisionByteCode','DivisionByteExecution','DivisionRefinement','DivisionImage','DivisionPackets','DivisionPacking','DivisionRegions','DivisionLinear','DivisionLayout','DivisionData','DivisionSetup','DivisionPaths','DivisionByteBlocks','DivisionByteSimulation','DivisionByteLoop','DivisionByteCorrect']])
    files=['native.asm','native.obj','native.lst','harness.obj','division.exe','run.log','native.disasm.txt','lean-control.json','lean-packets.json']
    report=dict(as_of=date.today().isoformat(),passed=True,architecture='x86',runs=runs,executions=sum(r['executions'] for r in runs),
      unsigned_nonzero=True,signed_truncation='toward zero',signed_quotient_overflow='MIN_INT/-1 excluded',
      signed_remainder_overflow_case='included: zero remainder',
      original_instruction_order=True,corrections='M06c and four M11 substitutions',
      full_gpr_stack_input_reuse_code_frame_checked=True,
      complete_lean_packet_comparison=True,whole_literal_execution_proof=True,
      whole_word_control_execution_proof=True,original_input_result_frame_purity_proof=True,
      scope='Finite corrected native Listing 12 evidence; whole word/control original-input result/carry/register/stack/frame/purity theorem checked in all four modes; all initial native packets/full owner words match Lean; actual byte-form effects/refinement/mutable packet preservation checked. The universal selected-x86 original-image byte theorem constructs the entire current-fetch trace, all four results, registers/stack/CF/PC, code-owned writes and the exact exterior-byte frame from initial placement and nonzero inputs. Physical ISA/configuration/fetch remains E05/A01.',
      foundation_proofs=lean['checked_division_foundation_declarations'],
      data_proofs=lean['checked_division_data_declarations'],literal_word_data_execution_proof=True,
      control_proofs=lean['checked_division_control_declarations'],actual_lean_control_geometry_checked=True,geometry=geometry,
      complete_word_proofs=lean['checked_division_complete_word_declarations'],
      byte_primitive_proofs=lean['checked_division_byte_primitives_declarations'],
      refinement_proofs=lean['checked_division_refinement_declarations'],
      image_proofs=lean['checked_division_image_declarations'],
      packet_proofs=lean['checked_division_packets_declarations'],packets=packets,
      byte_execution_proofs=lean['checked_division_byte_execution_declarations'],
      lean_audit_sha256=digest(ROOT/'validation/lean.json'),commands=commands,
      sources={s:digest(ROOT/s) for s in sources},
      artifacts={str((folder/f).relative_to(ROOT)):digest(folder/f) for f in files})
    (ROOT/'validation/division.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
