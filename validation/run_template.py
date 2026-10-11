"""Complete compile-bound template transfer; MASM bytes versus actual Lean bindings."""
from pathlib import Path
import hashlib,json,os,re,shutil
from run_defaddr import vc_environment,run
from lean_export import lean_command
ROOT=Path(__file__).resolve().parents[1]
MODS=['TemplateRelocation','TemplateCopy','StringMacroLayout','StringMacroImage','StringMacroEffects','StringMacroTrace','StringTemplate','ConversionOperands']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    lp=ROOT/'validation/lean.json';lean=json.loads(lp.read_text(encoding='utf-8'))
    names=lean['checked_native_template_copy_declarations'];assert lean['native_template_copy_checked']
    assert set(names)<={row['name'] for row in lean['declarations']}
    for name in MODS:
        p=ROOT/f'lean/SmcTuring/Native/{name}.lean';assert lean['sources'][str(p.relative_to(ROOT))]==digest(p)
    sources=['validation/run_template.py','validation/template_native.asm','validation/template_native.cpp','validation/transfer_native.asm',
      'smcTuring/listing5_smc.inc','smcTuring/pure_smc.inc','validation/run_defaddr.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportTemplate.lean']+[f'lean/SmcTuring/Native/{n}.lean' for n in MODS]
    report=dict(as_of='2026-10-05',passed=True,proofs=names,lean_audit_sha256=digest(lp),actual_lean_codec_checked=True,
      compilation_bindings_checked=True,whole_template_fetch_checked=True,original_image_construction_checked=True,
      original_image_theorem='SmcTuring.Native.TemplateCopy.original_image_correct',copy_theorem='SmcTuring.Native.TemplateCopy.correct',whole_address_theorem='SmcTuring.Native.TemplateCopy.original_addresses_correct',
      memory_target_theorem='SmcTuring.Native.TemplateRelocation.memory_target',call_target_theorem='SmcTuring.Native.TemplateRelocation.call_target',
      moffs_payload_theorem='SmcTuring.Native.TemplateCopy.moffs_payload',
      scope='Universal finite selected-form compiler binds internal/external MOFFS, all ten memory-operation absolute/RIP fields and near CALL fields for independently placed destination code. Packet lengths and source/destination forms/bytes are constructed. One constructed macro/blueprint image and static resources derive whole live TRANSFERDATA trace, complete destination template bytes, every actual destination fetch and address meaning under explicit signed reach. Native tests execute TRANSFERDATA and verify complete template byte copying/register/buffer/cursor/code/reuse; copied arbitrary template programs are decoded and address-checked rather than run as a universal template algorithm. Compile-time relocation is the paper-authorized route; physical ISA/configuration/fetch and other listing algorithms retain their scope.',
      sources={name:digest(ROOT/name) for name in sources},runs=[])
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    for arch in ['x86','x64']:
        folder=ROOT/'validation/.build/template'/arch;folder.mkdir(parents=True,exist_ok=True);env=vc_environment(arch)
        def tool(n):
            found=shutil.which(n,path=env['PATH']);assert found,n;return found
        commands=[]
        for stem in ['template','transfer']:
            obj=folder/(stem+'.obj')
            asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/Fo'+str(obj),'/Fl'+str(folder/(stem+'.lst')),'/I'+str(ROOT/'smcTuring')]
            asm+=['/DX64'] if arch=='x64' else ['/safeseh']
            asm+=[str(ROOT/f'validation/{stem}_native.asm')];commands.append(asm)
        commands += [[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/template_native.cpp'),'/Fo'+str(folder/'harness.obj')],
          [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'template.exe'),str(folder/'template.obj'),str(folder/'transfer.obj'),str(folder/'harness.obj')]]
        (folder/'build.log').write_text(''.join(run(c,folder,env) for c in commands),encoding='utf-8')
        out=run([str(folder/'template.exe')],folder,env);print(out.strip(),flush=True);(folder/'run.log').write_text(out,encoding='utf-8')
        assert 'PASS 768 executions; 4 forward/backward layouts' in out,out
        packets=json.loads((folder/'template-packets.json').read_text(encoding='utf-8'));assert len(packets)==4
        args=[arch]+[str(p[k]) for p in packets for k in ['start','source','destination','size','externalPC','externalField']]
        refs=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportTemplate.lean']+args),ROOT/'lean',export_env));assert len(refs)==4
        total_bytes=0;total_headers=0;word=4 if arch=='x86' else 8;limit=1<<(8*word)
        for packet,ref in zip(packets,refs):
            assert packet['size']==(83 if arch=='x86' else 103)
            assert packet['size']<1<<31 and packet['end']<limit
            for key in ['source','destination']:
                a=packet[key];n=max(packet['size'],word);assert a+n<limit
                assert a+n<=packet['start'] or packet['end']<=a
            s,d,n=packet['source'],packet['destination'],packet['size'];assert s+n<=d or d+n<=s
            for key in ['start','source','destination','size','sourceField','destinationField','body','bodyEnd','end','blueprint','macroBytes']:assert packet[key]==ref[key],(arch,key,packet,ref)
            assert packet['copied']==ref['blueprint']
            expected_pc=d;flattened=[]
            assert len(ref['packets'])==15
            for row in ref['packets']:
                assert row['pc']==expected_pc and row['length']==len(row['bytes']) and row['fetched'] and row['reachable']
                assert row['target']==row['resolved']
                assert row['target'] is None or row['target']<limit
                expected_pc+=row['length'];flattened+=row['bytes']
            assert expected_pc==d+n and flattened==packet['copied']
            total_bytes+=n;total_headers+=len(ref['packets'])
        assert [p['source']<p['destination'] for p in packets]==[True,False,True,False]
        (folder/'lean-packets.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
        (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'template.obj')],folder,env),encoding='utf-8')
        files=['template.obj','template.lst','transfer.obj','transfer.lst','harness.obj','template.exe','run.log','template-packets.json','lean-packets.json','native.disasm.txt']
        artifacts={str((folder/name).relative_to(ROOT)):digest(folder/name) for name in files}
        report['runs'].append(dict(architecture=arch,passed=True,executions=768,layouts=4,complete_templates=4,compared_template_bytes=total_bytes,
          instruction_headers=total_headers,all_memory_operations=10,commands=commands,artifacts=artifacts))
        print(f'{arch}: 4 complete relocated templates/{total_bytes} bytes/{total_headers} destination headers and all absolute/MOFFS/RIP/CALL targets match Lean',flush=True)
    (ROOT/'validation/template.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
