"""Build and regress minimally corrected literal Listing 11 on finite x86.
Host setup/observation are outside the pure loop. This is native evidence,
not a full byte-fetch/physical-ISA refinement theorem.
"""
from pathlib import Path
import hashlib,json,shutil,os
from audit_encoding import coff
from lean_export import lean_command
from run_branch import code_relocation_targets,encoded_address
from run_defaddr import vc_environment,run
ROOT=Path(__file__).resolve().parents[1]
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def check_geometry(code,symbols,reference):
    origin=symbols['MulPureBegin']
    names={'guard_continuation':'lbl0','guard':'MulGuardBegin','body_continuation':'lblbody',
           'body':'MulBodyBegin','exit_continuation':'lbl9','exit':'MulFinishBegin','end':'MulPureEnd'}
    for role,symbol in names.items():
        assert symbols[symbol]-origin==reference[role],(role,symbols[symbol]-origin,reference[role])
    initial,guard,body,finish=reference['data_lengths']
    assert [sum(lengths) for lengths in [initial,guard,body,finish]]==[44,65,130,20]
    assert symbols['MulEntryCall']==origin+sum(initial)+6
    assert symbols['lbl3']==symbols['MulGuardBegin']+sum(guard)+6
    assert symbols['MulBackCall']==symbols['MulBodyBegin']+sum(body)+6
    assert code[symbols['MulEntryCall']]==code[symbols['lbl3']]==code[symbols['MulBackCall']]==0xe8
    def word(at):return int.from_bytes(code[at:at+4],'little')
    assert word(symbols['MulEntryCall']+1)==word(symbols['lbl3']+1)==0
    assert word(symbols['MulBackCall']+1)==reference['back_delta']
    assert symbols['lbl9']-symbols['lblbody']==reference['delta']==171
    delta_store=symbols['MulGuardBegin']+sum(guard[:5])
    assert code[delta_store:delta_store+2]==bytes.fromhex('c705') and word(delta_store+6)==reference['delta']
    data_headers=[['c705','8705','a3','8705','8705','a3','8705'],
                  ['c705','f71d','831d','f71d','f715','c705','8125','8135'],
                  ['c705','8705','2105','8705','8705','a3','8705','c705','c705','f71d','831d','8125','8105','c705','d125','c705','d12d'],
                  ['c705','c705']]
    starts=[origin,symbols['MulGuardBegin'],symbols['MulBodyBegin'],symbols['MulFinishBegin']]
    count=0
    for start,lengths,headers in zip(starts,reference['data_lengths'],data_headers):
        assert len(lengths)==len(headers)
        cursor=start
        for length,header in zip(lengths,headers):
            expected=bytes.fromhex(header);assert code[cursor:cursor+len(expected)]==expected,(cursor,header)
            cursor+=length;count+=1
    for label in ['lbl0','lblbody','lbl9']:
        cursor=symbols[label]
        for length,header in [(6,'8725'),(7,'8305'),(6,'8705'),(5,'a3'),(6,'8705')]:
            expected=bytes.fromhex(header);assert code[cursor:cursor+len(expected)]==expected,(label,cursor,header)
            cursor+=length;count+=1
        assert cursor==symbols[label]+30
    for call in ['MulEntryCall','lbl3','MulBackCall']:
        assert code[symbols[call]-6:symbols[call]-4]==bytes.fromhex('8725');count+=2
    assert count==55
    return dict(lean_geometry_checked=True,pure_bytes=reference['end'],instruction_headers=count,delta=reference['delta'],
                back_delta=reference['back_delta'],source='selected word/control geometry plus independent native headers; full live-byte emitter remains open')

def check_packets(folder,code,symbols,reference):
    section,targets=code_relocation_targets(folder/'native.obj')
    checked=set();relocations=set();byte_count=0
    for group,base in [('literal_packets',symbols['MulPureBegin']),('owner_packets',0)]:
        for packet in reference[group]:
            pc=base+packet['offset'];expected=bytearray(packet['bytes'])
            local={position:target for position,target in targets.items() if pc<=position<pc+len(expected)}
            absolute={pc+offset for offset in packet['absolute_offsets']}
            assert set(local)==absolute,(pc,local,absolute)
            for offset in packet['absolute_offsets']:
                position=pc+offset
                value=int.from_bytes(expected[offset:offset+4],'little')
                expected[offset:offset+4]=encoded_address(value,position,targets,section)
                relocations.add(position)
            assert code[pc:pc+len(expected)]==expected,(group,pc,code[pc:pc+len(expected)].hex(),expected.hex())
            assert not checked.intersection(range(pc,pc+len(expected))),'Overlapping complete packets'
            checked.update(range(pc,pc+len(expected)));byte_count+=len(expected)
    assert len(reference['literal_packets'])==55 and len(reference['owner_packets'])==4
    assert byte_count==422 and len(relocations)==57
    expected_fields=[symbols['MulInputX']+6,symbols['MulInputY']+6,symbols['MulResult']+6,
        symbols['lbl7']+6,symbols['lbl8']+6,symbols['lbl10']+6,symbols['lbl1']+6,
        symbols['lbl2']+6,symbols['lbl3']+1,symbols['lbl4']+6,symbols['lbl5']+6,
        symbols['lbl6']+6,symbols['stptr']+6,symbols['stptr']+2]
    assert reference['field_coordinates']==expected_fields
    ordered=sorted(expected_fields)
    assert all(first+4<=second for first,second in zip(ordered,ordered[1:]))
    image_packets=reference['initial_image_packets']
    assert len(image_packets)==59
    assert sorted(reference['initial_image_fields'])==sorted(expected_fields)
    native_owners={symbols[label]:[symbols[label]+offset] for label,offset in
        [('lbl1',6),('lbl2',6),('lbl3',1),('lbl4',6),('lbl5',6),('lbl6',6),
         ('lbl7',6),('lbl8',6),('lbl10',6),('MulInputX',6),('MulInputY',6),('MulResult',6)]}
    native_owners[symbols['stptr']]=[symbols['stptr']+2,symbols['stptr']+6]
    seen=set();seen_fields=[]
    for packet in image_packets:
        pc=packet['offset'];expected=bytearray(packet['bytes'])
        assert packet['owned_fields']==native_owners.get(pc,[]),(pc,packet['owned_fields'],native_owners.get(pc,[]))
        seen_fields.extend(packet['owned_fields'])
        local={position for position in targets if pc<=position<pc+len(expected)}
        assert local=={pc+offset for offset in packet['absolute_offsets']}
        for offset in packet['absolute_offsets']:
            value=int.from_bytes(expected[offset:offset+4],'little')
            expected[offset:offset+4]=encoded_address(value,pc+offset,targets,section)
        assert code[pc:pc+len(expected)]==expected,('initial_image',pc)
        assert not seen.intersection(range(pc,pc+len(expected)))
        seen.update(range(pc,pc+len(expected)))
        assert all(pc<=field and field+4<=pc+len(expected) for field in packet['owned_fields'])
    assert seen==checked and seen_fields==reference['initial_image_fields'] and len(seen_fields)==14
    return dict(complete_packets_checked=True,executed_packets=55,inactive_owner_packets=4,
        compared_bytes=byte_count,address_relocations=len(relocations),operand_fields=len(expected_fields),
        initial_image_packets=59,image_owners_checked=True,mutable_image_fields=14,
        scope='Initial emitted byte packets, destinations, mutable owners/constants and complete DIR32 symbol/section/addend placement; continuous current-byte execution remains open')

def main():
    lean_path=ROOT/'validation/lean.json'
    lean=json.loads(lean_path.read_text(encoding='utf-8'))
    proofs=[]
    for module in ['MultiplyAlgebra','MultiplyWords','MultiplyLoop','MultiplyControl','MultiplyBlocks','MultiplyExecution','MultiplyByteCode','MultiplyByteExecution','MultiplyRefinement','MultiplyPackets','MultiplyImage','MultiplyPacking','MultiplyRegions','MultiplyLayout','MultiplyData','MultiplyLinear','MultiplySetup','MultiplyPaths','MultiplyByteBlocks','MultiplyByteSimulation','MultiplyByteLoop','MultiplyByteCorrect']:
        proof=ROOT/f'lean/SmcTuring/Appendix/{module}.lean'
        assert lean['sources'][str(proof.relative_to(ROOT))]==digest(proof),'Refresh the Lean audit first'
        proofs += [item['name'] for item in lean['declarations'] if item['name'].startswith(f'SmcTuring.Appendix.{module}.')]
    assert len(proofs)==329
    folder=ROOT/'validation/.build/multiplication';folder.mkdir(parents=True,exist_ok=True)
    env=vc_environment('x86')
    def tool(name):
        found=shutil.which(name,path=env['PATH']);assert found,name;return found
    commands=[
        [tool('ml.exe'),'/nologo','/c','/safeseh','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst'),str(ROOT/'validation/multiplication_native.asm')],
        [tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/multiplication_native.cpp'),'/Fo'+str(folder/'harness.obj')],
        [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'multiplication.exe'),str(folder/'harness.obj'),str(folder/'native.obj')]]
    (folder/'build.log').write_text(''.join(run(command,folder,env) for command in commands),encoding='utf-8')
    output=run([str(folder/'multiplication.exe')],folder,env)
    assert 'Listing 11 x86: PASS 11458 cases' in output,output
    (folder/'run.log').write_text(output,encoding='utf-8')
    (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    code,symbols,relocations=coff(folder/'native.obj','x86')
    coordinates=[symbols[name] for name in ['MulPureBegin','MulInputX','MulInputY','MulResult','stptr']]
    reference=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportMultiply.lean']+list(map(str,coordinates))),ROOT/'lean',export_env))
    (folder/'lean-geometry.json').write_text(json.dumps(reference,indent=2)+'\n',encoding='utf-8')
    geometry=check_geometry(code,symbols,reference)
    packets=check_packets(folder,code,symbols,reference)
    sources=['validation/run_multiplication.py','validation/multiplication_native.asm','validation/multiplication_native.cpp','validation/run_defaddr.py','validation/audit_encoding.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportMultiply.lean',
             'lean/SmcTuring/Appendix/MultiplyAlgebra.lean','lean/SmcTuring/Appendix/MultiplyWords.lean','lean/SmcTuring/Appendix/MultiplyLoop.lean','lean/SmcTuring/Appendix/MultiplyControl.lean','lean/SmcTuring/Appendix/MultiplyBlocks.lean','lean/SmcTuring/Appendix/MultiplyExecution.lean','lean/SmcTuring/Appendix/MultiplyByteCode.lean','lean/SmcTuring/Appendix/MultiplyByteExecution.lean','lean/SmcTuring/Appendix/MultiplyRefinement.lean','lean/SmcTuring/Appendix/MultiplyPackets.lean','validation/run_branch.py','validation/generate_branch.py','lean/SmcTuring/Appendix/MultiplyImage.lean','lean/SmcTuring/Appendix/MultiplyPacking.lean','lean/SmcTuring/Appendix/MultiplyRegions.lean','lean/SmcTuring/Appendix/MultiplyLayout.lean','lean/SmcTuring/Appendix/MultiplyData.lean','lean/SmcTuring/Appendix/MultiplyLinear.lean','lean/SmcTuring/Appendix/MultiplySetup.lean','lean/SmcTuring/Appendix/MultiplyPaths.lean','lean/SmcTuring/Appendix/MultiplyByteBlocks.lean','lean/SmcTuring/Appendix/MultiplyByteSimulation.lean','lean/SmcTuring/Appendix/MultiplyByteLoop.lean','lean/SmcTuring/Appendix/MultiplyByteCorrect.lean']
    report=dict(as_of='2026-10-05',passed=True,architecture='x86',cases=11458,operand_words=14,incoming_carry_cases=2,
                scope='M07 literal Listing 11 finite native regression: product, all operand/scratch/stack words, GPRs/ESP/CF, exterior code bytes and repeated calls; complete original-image selected-byte execution now proves all-input low-word product/termination, actual guard/body/backedge/exit PC dispatch, EAX/ESP/CF/inputs, only owned writes, reusable image/stack values and exact original exterior bytes outside ten scratch/result fields; full physical ISA/configuration/fetch realization remains open',
                sources={name:digest(ROOT/name) for name in sources},lean_audit_sha256=digest(lean_path),proofs=proofs,whole_byte_correctness_checked=True,byte_correctness_theorem='SmcTuring.Appendix.MultiplyByteCorrect.correct',byte_scratch_fields=10,commands=commands,output=output,geometry=geometry,packets=packets,
                artifacts={str(path.relative_to(ROOT)):digest(path) for path in [folder/'native.obj',folder/'native.lst',folder/'native.disasm.txt',folder/'multiplication.exe',folder/'run.log',folder/'lean-geometry.json']})
    (ROOT/'validation/multiplication.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(output.strip(),flush=True)
if __name__=='__main__': main()
