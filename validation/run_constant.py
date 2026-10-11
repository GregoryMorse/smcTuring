"""M08 Listing 6 native regression and independent complete-packet comparator."""
from pathlib import Path
import hashlib,json,os,re,shutil
from lean_export import lean_command
from run_defaddr import vc_environment,run
ROOT=Path(__file__).resolve().parents[1]
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def literal_baseline():
    # The published compile-time listing: leading zeros, unincremented runtime gaps.
    # Unsigned 32-bit constants and x86 count masking make this finite and reproducible.
    def clz(n):return 32-n.bit_length()
    def right(n,count):return n>>count
    def coefficient(n):
        factor=(1<<(clz(n)&31))&0xffffffff
        n=right(n,clz(n)+1)
        if not n:return factor
        total=factor;factor=(factor<<(clz(n)&31))&0xffffffff
        n=right(n,clz(n)+1)
        while n:
            total=(total+factor)&0xffffffff
            factor=(factor<<(clz(n)&31))&0xffffffff
            n=right(n,clz(n)+1)
        return (factor+total)&0xffffffff
    constants=[0,1,2,3,5,7,0x7fffffff,0x80000000,0xffffffff]
    rows=[dict(constant=n,actual=coefficient(n),expected=n) for n in constants]
    assert any(row['actual']!=row['expected'] for row in rows)
    return dict(scope='Reconstructed printed constant-emitter coefficient baseline; unchanged original C++/ASM comparison baseline is recorded separately',
                rows=rows,source='validation/.cache/morse-2018.pdf',source_sha256=digest(ROOT/'validation/.cache/morse-2018.pdf'))
def packet(op,data,scratch):
    kind,count=op['kind'],op['count']
    def word(n):return int(n).to_bytes(4,'little')
    if kind==0:return bytes.fromhex('c705')+word(data)+word(0)
    if kind==1:
        assert 1<=count<=31
        return bytes([0xd1 if count==1 else 0xc1,0x25])+word(data)+(b'' if count==1 else bytes([count]))
    if kind==2:return bytes.fromhex('8705')+word(data)
    if kind==3:return bytes([0xa3])+word(scratch)
    if kind==4:return bytes.fromhex('0105')+word(scratch)
    if kind==5:return bytes.fromhex('8105')+word(data)+word(0x12345678)
    raise AssertionError(op)
def main():
    lean_path=ROOT/'validation/lean.json';lean=json.loads(lean_path.read_text(encoding='utf-8'))
    modules=['ConstantAlgebra','ConstantWords','ConstantByteCode','ConstantByteExecution','ConstantRefinement','ConstantImage','ConstantPacking','ConstantData','ConstantSimulation','ConstantShape','ConstantRegions','ConstantGeometry','ConstantCorrect'];proofs=[]
    for module in modules:
        path=ROOT/f'lean/SmcTuring/Appendix/{module}.lean'
        assert lean['sources'][str(path.relative_to(ROOT))]==digest(path),'Refresh Lean audit first'
        proofs += [item['name'] for item in lean['declarations'] if item['name'].startswith(f'SmcTuring.Appendix.{module}.')]
    assert len(proofs)==184, len(proofs)
    baseline=literal_baseline()
    folder=ROOT/'validation/.build/constant';folder.mkdir(parents=True,exist_ok=True)
    env=vc_environment('x86')
    def tool(name):
        found=shutil.which(name,path=env['PATH']);assert found,name;return found
    commands=[
        [tool('ml.exe'),'/nologo','/c','/safeseh','/Fo'+str(folder/'native.obj'),str(ROOT/'validation/constant_native.asm')],
        [tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/constant_native.cpp'),'/Fo'+str(folder/'harness.obj')],
        [tool('link.exe'),'/nologo','/CETCOMPAT:NO','/OUT:'+str(folder/'constant.exe'),str(folder/'harness.obj'),str(folder/'native.obj')]]
    (folder/'build.log').write_text(''.join(run(command,folder,env) for command in commands),encoding='utf-8')
    output=run([str(folder/'constant.exe')],folder,env);print(output.strip(),flush=True)
    (folder/'run.log').write_text(output,encoding='utf-8')
    match=re.search(r'PASS (\d+) cases; (\d+) constants; (\d+) pure packets',output);assert match,output
    cases,constant_count,packet_count=map(int,match.groups())
    records=json.loads((folder/'constant-packets.json').read_text(encoding='utf-8'))
    assert len(records)==constant_count
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    reference=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportConstant.lean']+[str(r['constant']) for r in records]),ROOT/'lean',export_env))
    (folder/'lean-programs.json').write_text(json.dumps(reference,indent=2)+'\n',encoding='utf-8')
    packets=byte_count=0
    for record,ref in zip(records,reference):
        assert record['constant']==ref['constant']
        base=record['base'];data=base+record['data'];scratch=base+record['scratch']
        def native_packet(raw,absolute):
            result=bytearray(raw)
            for offset in absolute:
                role=int.from_bytes(result[offset:offset+4],'little')
                assert role in [0,1]
                result[offset:offset+4]=(data if role==0 else scratch).to_bytes(4,'little')
            return bytes(result)
        assert len(ref['packets'])==len(ref['program'])
        emitted=[];owners=[];cursor=0
        for op,pkt in zip(ref['program'],ref['packets']):
            actual=native_packet(pkt['bytes'],pkt['absolute_offsets'])
            assert actual==packet(op,data,scratch)
            emitted.append(actual)
            owners.extend(cursor+offset for offset in pkt['owned_offsets'])
            cursor+=len(actual)
        program=b''.join(emitted)
        assert len(program)==record['pure']
        assert record['data']==len(program)+7
        final=[i for i,op in enumerate(ref['program']) if op['kind']==5]
        if final:
            assert final==[len(ref['program'])-1]
            expected_scratch=len(program)-4
        else:expected_scratch=record['data']+10
        assert record['scratch']==expected_scratch
        assert owners==([record['scratch']] if final else [])
        assert abs(data-scratch)>=4
        expected=program+bytes([0xc3])+native_packet(ref['data_owner'],[2])
        if not final:expected+=native_packet(ref['inactive_scratch_owner'],[2])
        assert bytes(record['bytes'])==expected,record['constant']
        geometry=ref['geometry']
        assert (geometry['pure'],geometry['data'],geometry['scratch'],geometry['extent'])==(record['pure'],record['data'],record['scratch'],len(expected))
        assert len(geometry['entries'])==len(ref['program'])+(1 if final else 2)
        geometry_fields=[]
        for entry in geometry['entries']:
            actual=bytearray(entry['bytes'])
            for offset in entry['absolute_offsets']:
                address=int.from_bytes(actual[offset:offset+4],'little')
                assert address in [geometry['data'],geometry['scratch']]
                actual[offset:offset+4]=(base+address).to_bytes(4,'little')
            assert bytes(record['bytes'][entry['pc']:entry['pc']+len(actual)])==actual
            geometry_fields.extend(entry['fields'])
        assert geometry_fields==([record['scratch'],record['data']] if final else [record['data'],record['scratch']])

        packets+=len(ref['program']);byte_count+=len(expected)
    assert packets==packet_count
    sources=['validation/run_constant.py','validation/constant_native.asm','validation/constant_native.cpp',
        'validation/run_defaddr.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportConstant.lean']+[f'lean/SmcTuring/Appendix/{module}.lean' for module in modules]
    report=dict(as_of='2026-10-05',passed=True,architecture='x86',cases=cases,constants=constant_count,
        pure_packets=packets,compared_bytes=byte_count,complete_packets_checked=True,proofs=proofs,
        word_proofs=lean['checked_appendix_constant_word_declarations'],byte_proofs=lean['checked_appendix_constant_byte_declarations'],
        geometry_proofs=lean['checked_appendix_constant_geometry_declarations'],
        actual_lean_codec_checked=True,static_byte_trace_checked=True,
        byte_trace_theorem='SmcTuring.Appendix.ConstantSimulation.original_image_correct',
        variable_emitter_layout_derived=True,complete_geometry_codec_checked=True,
        emitter_correct_theorem='SmcTuring.Appendix.ConstantCorrect.correct',
        reusable_trace_theorem='SmcTuring.Appendix.ConstantCorrect.reusable_trace',
        reusable_correct_theorem='SmcTuring.Appendix.ConstantCorrect.reusable_correct',
        lean_audit_sha256=digest(lean_path),baseline=baseline,commands=commands,output=output,
        scope='Corrected printed constant emitter: all-input Lean Word32 product/compiled trace/accumulator/purity/legal shifts/exterior-word frame; finite x86 product/scratch/GPRs/ESP/CF/exterior bytes/reuse and complete emitted packet comparator. All-input original-image live-byte trace/product/restoration/purity/exterior-byte frame/CF/endpoint is checked from only original initialization, entry and full image extent capacity. All packet placement, own operands, ownership and separation are derived for the variable emitter; reusable live fetch uses the preserved invariant. Physical ISA/fetch remains open.',
        sources={name:digest(ROOT/name) for name in sources},
        artifacts={str(path.relative_to(ROOT)):digest(path) for path in [folder/'constant.exe',folder/'native.obj',folder/'harness.obj',folder/'run.log',folder/'constant-packets.json',folder/'lean-programs.json']})
    (ROOT/'validation/constant.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'Listing 6 comparator: {packets} complete pure packets; {byte_count} total original image bytes',flush=True)
if __name__=='__main__':main()
