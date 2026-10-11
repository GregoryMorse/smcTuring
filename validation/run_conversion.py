"""Listing 6 full-width conversion: actual Lean packets and finite native regressions."""
from pathlib import Path
import hashlib,json,os,re,shutil
from run_defaddr import vc_environment,run
from lean_export import lean_command
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    lp=ROOT/'validation/lean.json';lean=json.loads(lp.read_text(encoding='utf-8'))
    names=lean['checked_native_conversion_declarations'];assert lean['native_conversion_checked']
    assert set(names)<={row['name'] for row in lean['declarations']}
    for name in ['ConversionLayout','ConversionEffects','ConversionImage','ConversionOperands','ConversionOwnership']:
        p=ROOT/f'lean/SmcTuring/Native/{name}.lean';assert lean['sources'][str(p.relative_to(ROOT))]==digest(p)
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    sources=['validation/run_conversion.py','validation/conversion_native.asm','validation/conversion_native.cpp','smcTuring/listing6_conversion.inc',
             'validation/run_defaddr.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportConversion.lean']+[f'lean/SmcTuring/Native/{n}.lean' for n in ['ConversionLayout','ConversionEffects','ConversionImage','ConversionOperands','ConversionOwnership']]
    report=dict(as_of='2026-10-05',passed=True,proofs=names,lean_audit_sha256=digest(lp),actual_lean_codec_checked=True,admissible_geometry_checked=True,owner_packets_codec_checked=True,
      corrected_theorem='SmcTuring.Native.ConversionImage.correct',original_image_theorem='SmcTuring.Native.ConversionImage.original_image_correct',
      scope='Universal selected x86/x64 full-word, current-byte conversion trace, source/accumulator/stack/carry restoration, endpoint, complete exterior bytes and patched MOFFS decoding. Ordinary-data import/export retain their initialization/observation scope. Finite native regressions and actual Lean codec comparison; physical/full-CPU refinement remains E05.',
      sources={name:digest(ROOT/name) for name in sources},runs=[])
    for arch in ['x86','x64']:
        folder=ROOT/'validation/.build/conversion'/arch;folder.mkdir(parents=True,exist_ok=True);env=vc_environment(arch)
        def tool(n):
            found=shutil.which(n,path=env['PATH']);assert found,n;return found
        asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst'),'/I'+str(ROOT/'smcTuring')]
        asm+=['/DX64'] if arch=='x64' else ['/safeseh'];asm+=[str(ROOT/'validation/conversion_native.asm')]
        commands=[asm,[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/conversion_native.cpp'),'/Fo'+str(folder/'harness.obj')],
          [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'conversion.exe'),str(folder/'native.obj'),str(folder/'harness.obj')]]
        (folder/'build.log').write_text(''.join(run(c,folder,env) for c in commands),encoding='utf-8')
        out=run([str(folder/'conversion.exe')],folder,env);print(out.strip(),flush=True);(folder/'run.log').write_text(out,encoding='utf-8')
        result=re.search(r'PASS (\d+) executions; (\d+) live words; 6 layouts',out);assert result,out
        cases,words=map(int,result.groups());assert cases==words*48 and words>=440
        packets=json.loads((folder/'conversion-packets.json').read_text(encoding='utf-8'));assert len(packets)==6
        refs=[];owner_count=0;owner_bytes=0
        for packet in packets:
            width=4 if arch=='x86' else 8;limit=1<<(8*width)
            start,end,source,dest=[packet[k] for k in ['start','end','source','destination']]
            assert end<limit and source+width<=limit and dest+width<=limit
            assert source+width<=dest or dest+width<=source
            for field in [source,dest]:assert field+width<=start or end<=field
            if arch=='x64':
                for pc,target in [(start+7,source),(start+14,dest),(end,source)]:assert -(1<<31)<=target-pc<(1<<31)
            args=[arch]+[str(packet[key]) for key in ['start','source','destination']]
            ref=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportConversion.lean']+args),ROOT/'lean',export_env))
            assert ref['end']==packet['end'] and ref['span']==(17 if arch=='x86' else 21)
            assert len(ref['packets'])==3
            assert [byte for p in ref['packets'] for byte in p['bytes']]==packet['bytes'],(arch,packet['name'],ref,packet)
            assert ref['source']==packet['source'] and ref['destination']==packet['destination']
            for owner in packet['owners']:
                assert owner['field']==owner['pc']+(1 if arch=='x86' else 2)
                assert owner['bytes']==ref['ownerZeroBytes']
                owner_count+=1;owner_bytes+=len(owner['bytes'])
            refs.append(dict(name=packet['name'],reference=ref))
        assert owner_count==8
        (folder/'lean-packets.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
        (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
        artifacts={str(p.relative_to(ROOT)):digest(p) for p in [folder/'native.obj',folder/'native.lst',folder/'harness.obj',folder/'conversion.exe',folder/'run.log',folder/'conversion-packets.json',folder/'lean-packets.json',folder/'native.disasm.txt']}
        report['runs'].append(dict(architecture=arch,passed=True,executions=cases,live_words=words,layouts=6,complete_helper_packets=18,complete_owner_packets=owner_count,complete_owner_bytes=owner_bytes,complete_helper_bytes=sum(len(p['bytes']) for p in packets),commands=commands,artifacts=artifacts))
    (ROOT/'validation/conversion.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
