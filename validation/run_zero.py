"""M09 positive DEFZERO native/full-packet regression, with typed literal baseline."""
from pathlib import Path
import hashlib,json,os,re,shutil
from run_defaddr import vc_environment,run
from lean_export import lean_command
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    lp=ROOT/'validation/lean.json';lean=json.loads(lp.read_text(encoding='utf-8'))
    proof=ROOT/'lean/SmcTuring/Appendix/ZeroImage.lean'
    assert lean['sources'][str(proof.relative_to(ROOT))]==digest(proof),'Refresh full Lean audit first'
    names=lean['checked_appendix_zero_declarations'];assert len(names)==18 and lean['appendix_zero_checked']
    assert set(names)<={row['name'] for row in lean['declarations']}
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    reference=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportZero.lean']),ROOT/'lean',export_env))
    assert reference['fields']==[6] and reference['length']==10
    sources=['validation/run_zero.py','validation/zero_native.asm','validation/zero_native.cpp','smcTuring/listing6_smc.inc',
             'validation/run_defaddr.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportZero.lean','lean/SmcTuring/Appendix/ZeroImage.lean']
    report=dict(as_of='2026-10-05',passed=True,proofs=names,lean_audit_sha256=digest(lp),actual_lean_codec_checked=True,
      corrected_theorem='SmcTuring.Appendix.ZeroImage.correct',original_image_theorem='SmcTuring.Appendix.ZeroImage.original_image_correct',
      scope='All-live-DWORD x86 current-byte proof of corrected one-instruction DEFZERO, register/PC/CF/ownership/exterior-byte/reusable-image contract. Both-architecture finite native regression; literal x64 RIP addressing checked independently, physical/full-CPU refinement remains open.',
      sources={name:digest(ROOT/name) for name in sources},runs=[])
    for arch in ['x86','x64']:
        folder=ROOT/'validation/.build/zero'/arch;folder.mkdir(parents=True,exist_ok=True);env=vc_environment(arch)
        def tool(n):
            found=shutil.which(n,path=env['PATH']);assert found,n;return found
        asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst'),'/I'+str(ROOT/'smcTuring')]
        asm+=['/DX64'] if arch=='x64' else ['/safeseh'];asm+=[str(ROOT/'validation/zero_native.asm')]
        commands=[asm,[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/zero_native.cpp'),'/Fo'+str(folder/'harness.obj')],
          [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'zero.exe'),str(folder/'native.obj'),str(folder/'harness.obj')]]
        (folder/'build.log').write_text(''.join(run(c,folder,env) for c in commands),encoding='utf-8')
        out=run([str(folder/'zero.exe')],folder,env);print(out.strip(),flush=True);(folder/'run.log').write_text(out,encoding='utf-8')
        result=re.search(r'PASS (\d+) executions; (\d+) live words',out);assert result,out
        cases,words=map(int,result.groups());assert cases==words*16 and words>=580
        baseline=re.search(r'before=([0-9a-f]+) after=([0-9a-f]+)',out);assert baseline,out
        before,after=(int(v,16) for v in baseline.groups());assert before==after and before!=0
        packets=json.loads((folder/'zero-packets.json').read_text(encoding='utf-8'));printed,corrected=packets
        assert printed['bytes'][:2]==[0x83,0x35] and printed['bytes'][6]==0 and printed['bytes'][7]==0xc3
        assert corrected['bytes'][10]==0xc3
        actual=bytearray(corrected['bytes'][:10]);address=int.from_bytes(actual[2:6],'little')
        if arch=='x86':assert address==corrected['pc']+6
        else:assert int.from_bytes(actual[2:6],'little',signed=True)==-4
        actual[2:6]=(6).to_bytes(4,'little');assert list(actual)==reference['bytes']
        (folder/'lean-packet.json').write_text(json.dumps(reference,indent=2)+'\n',encoding='utf-8')
        (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
        artifacts={str(p.relative_to(ROOT)):digest(p) for p in [folder/'native.obj',folder/'native.lst',folder/'harness.obj',folder/'zero.exe',folder/'run.log',folder/'zero-packets.json',folder/'lean-packet.json',folder/'native.disasm.txt']}
        report['runs'].append(dict(architecture=arch,passed=True,executions=cases,live_words=words,baseline=dict(typed_literal_opcode=0x83,immediate_bytes=1,field_before=before,field_after=after),corrected_immediate_bytes=4,own_field_offset=6,commands=commands,artifacts=artifacts))
    (ROOT/'validation/zero.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
