"""M10 positive TRANSFERDATA regression and actual complete Lean packet comparison."""
from pathlib import Path
import hashlib,json,os,re,shutil
from run_defaddr import vc_environment,run
from lean_export import lean_command
ROOT=Path(__file__).resolve().parents[1]
MODS=['StringCopy','StringPlan','StringCursor','StringFields','StringCodec','StringForm','StringExecution','StringMoves','StringMoveTrace','StringTemplate','StringOperands','StringWindow','StringInit','StringRestore','StringInitTrace','StringSetup','StringSetupTrace','StringProgram','StringMacroLayout','StringMacroImage','StringMacroEffects','StringMacroTrace']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    lp=ROOT/'validation/lean.json';lean=json.loads(lp.read_text(encoding='utf-8'))
    names=lean['checked_native_string_copy_declarations'];assert lean['native_string_copy_checked']
    execution_names=lean['checked_native_string_execution_declarations'];assert lean['native_string_execution_checked']
    stage_names=lean['checked_native_string_stage_declarations'];assert lean['native_string_stages_checked']
    macro_names=lean['checked_native_string_macro_declarations'];assert lean['native_string_macro_checked']
    assert set(names+execution_names+stage_names+macro_names)<={row['name'] for row in lean['declarations']}
    for name in MODS:
        p=ROOT/f'lean/SmcTuring/Native/{name}.lean';assert lean['sources'][str(p.relative_to(ROOT))]==digest(p)
    binary=ROOT/'lean/.elan/toolchains'/lean['toolchain'].replace('/','--').replace(':','---')/'bin'
    export_env=dict(os.environ);export_env['PATH']=str(binary)+os.pathsep+export_env['PATH']
    sources=['validation/run_transfer.py','validation/transfer_native.asm','validation/transfer_native.cpp','smcTuring/listing5_smc.inc','smcTuring/pure_smc.inc',
             'validation/run_defaddr.py','validation/lean_build.py','validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py','lean/ExportTransfer.lean']+[f'lean/SmcTuring/Native/{n}.lean' for n in MODS]
    report=dict(as_of='2026-10-05',passed=True,proofs=names,execution_proofs=execution_names,stage_proofs=stage_names,macro_proofs=macro_names,continuous_macro_trace_checked=True,complete_final_state_checked=True,static_macro_resources_checked=True,initializer_trace_checked=True,prefix_trace_checked=True,restoration_pairs_checked=True,actual_program_encoding_checked=True,selected_body_current_fetch_checked=True,live_macro_decoding_checked=True,lean_audit_sha256=digest(lp),actual_lean_codec_checked=True,complete_macro_packets_checked=True,
      macro_trace_theorem='SmcTuring.Native.StringMacroTrace.correct',macro_effect_theorem='SmcTuring.Native.StringMacroTrace.run_correct',macro_reuse_theorem='SmcTuring.Native.StringMacroTrace.reusable',macro_range_theorem='SmcTuring.Native.StringMacroLayout.tail_ranges',
      prefix_theorem='SmcTuring.Native.StringSetupTrace.initialized_trace',prefix_effect_theorem='SmcTuring.Native.StringSetup.effect',restoration_theorem='SmcTuring.Native.StringRestore.trace',program_encoding_theorem='SmcTuring.Native.StringProgram.encoding',
      body_theorem='SmcTuring.Native.StringMoveTrace.correct',copied_packet_theorem='SmcTuring.Native.StringTemplate.copied_fetch',rip_relocation_theorem='SmcTuring.Native.StringTemplate.rip_target',
      byte_copy_theorem='SmcTuring.Native.StringPlan.correct',cursor_theorem='SmcTuring.Native.StringCursor.pair_correct',memory_theorem='SmcTuring.Native.StringFields.effect',
      scope='Selected forward MOVS byte-copy, literal width-plan equivalence, SI/DI/pointer-field modular restoration and exact unified-byte effect/frame are universal. Finite literal x86/x64 native whole-macro execution and complete byte/field/PC encoding comparison include corrected DEFDATA prefixes (x64 AX equals original first destination word). Selected actual-PC/current-byte MOVS body execution and copied-packet fetch/internal RIP/external absolute target laws are checked from initial bytes/static bounds. Exact both-mode initializer/prefix live-fetch traces and prefix register/memory effects, restoration-pair fetch/effects and complete legal emitted-program encoding are checked. A single original macro image and static full-word/copy/code bounds derive continuous whole-macro live-byte execution, exact full final state, both saved cursor loads, complete code/source frames, reentry readiness and computed backward rel32 reach. Whole-template absolute/MOFFS patching and physical ISA/configuration remain P04/E05.',
      sources={name:digest(ROOT/name) for name in sources},runs=[])
    for arch in ['x86','x64']:
        folder=ROOT/'validation/.build/transfer'/arch;folder.mkdir(parents=True,exist_ok=True);env=vc_environment(arch)
        def tool(n):
            found=shutil.which(n,path=env['PATH']);assert found,n;return found
        asm=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst'),'/I'+str(ROOT/'smcTuring')]
        asm+=['/DX64'] if arch=='x64' else ['/safeseh'];asm+=[str(ROOT/'validation/transfer_native.asm')]
        commands=[asm,[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/transfer_native.cpp'),'/Fo'+str(folder/'harness.obj')],
          [tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'transfer.exe'),str(folder/'native.obj'),str(folder/'harness.obj')]]
        (folder/'build.log').write_text(''.join(run(c,folder,env) for c in commands),encoding='utf-8')
        out=run([str(folder/'transfer.exe')],folder,env);print(out.strip(),flush=True);(folder/'run.log').write_text(out,encoding='utf-8')
        result=re.search(r'PASS (\d+) executions; (\d+) sizes',out);assert result,out
        cases,sizes=map(int,result.groups());assert cases==6144 and sizes==48
        assert 'intended buffers restored/unchanged' in out and 'payload selects other buffers' in out
        packets=json.loads((folder/'transfer-packets.json').read_text(encoding='utf-8'));assert len(packets)==sizes
        args=[arch]+[str(p[key]) for p in packets for key in ['start','source','destination','size']]
        refs=json.loads(run(lean_command(ROOT/'lean',binary,['--run','ExportTransfer.lean']+args),ROOT/'lean',export_env));assert len(refs)==sizes
        total_bytes=0;headers=0
        width=4 if arch=='x86' else 8;limit=1<<(8*width)
        for packet,ref in zip(packets,refs):
            assert 0<=packet['size']<1<<31 and packet['end']<limit
            assert len(packet['bytes'])<1<<31
            for key in ['source','destination']:
                address=packet[key];span=max(packet['size'],width)
                assert address+span<limit
                assert address+span<=packet['start'] or packet['end']<=address
            assert packet['source']+packet['size']<=packet['destination'] or packet['destination']+packet['size']<=packet['source']
            assert packet['sourceField']+width<=packet['destinationField'] and packet['destinationField']+width<=packet['body']
            exchange=6 if arch=='x86' else 7;subtract=(7 if arch=='x86' else 8)+(0 if packet['size']<128 else 3)
            destination_tail=packet['bodyEnd']+exchange+subtract
            for field,nextpc in [(packet['sourceField'],packet['bodyEnd']+exchange),(packet['sourceField'],destination_tail),(packet['destinationField'],destination_tail+exchange),(packet['destinationField'],packet['end'])]:
                assert -(1<<31)<=field-nextpc<1<<31
            for key in ['size','start','end','sourceField','destinationField','body','bodyEnd']:assert ref[key]==packet[key],(arch,key,packet,ref)
            assert ref['bytes']==packet['bytes'],(arch,packet['size'],ref,packet)
            assert ref['programBytes']==packet['bytes'] and ref['programInstructions']==len(ref['widths'])+(8 if arch=='x86' else 14)
            assert len(ref['prefixBytes'])==packet['body']-packet['start'] and ref['prefixBytes']==packet['bytes'][:len(ref['prefixBytes'])]
            assert sum(ref['widths'])==packet['size'] and all(w in ([1,2,4] if arch=='x86' else [1,2,4,8]) for w in ref['widths'])
            offset=packet['body']-packet['start'];assert packet['bytes'][offset:offset+len(ref['bodyBytes'])]==ref['bodyBytes']
            for field,key in [('sourceField','source'),('destinationField','destination')]:
                offset=packet[field]-packet['start'];assert int.from_bytes(bytes(packet['bytes'][offset:offset+width]),'little')==packet[key]
            decoded=ref['decodedPacketLengths'];body_decoded=ref['decodedBodyLengths']
            assert decoded is not None and body_decoded is not None
            assert len(decoded)==len(ref['widths'])+(8 if arch=='x86' else 14)
            assert sum(decoded)==len(packet['bytes']) and sum(body_decoded)==len(ref['bodyBytes'])
            assert len(body_decoded)==len(ref['widths']) and all(0<length<=15 for length in decoded)
            total_bytes+=len(packet['bytes']);headers+=len(decoded)
        (folder/'lean-packets.json').write_text(json.dumps(refs,indent=2)+'\n',encoding='utf-8')
        (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
        artifacts={str(p.relative_to(ROOT)):digest(p) for p in [folder/'native.obj',folder/'native.lst',folder/'harness.obj',folder/'transfer.exe',folder/'run.log',folder/'transfer-packets.json',folder/'lean-packets.json',folder/'native.disasm.txt']}
        report['runs'].append(dict(architecture=arch,passed=True,executions=cases,sizes=sizes,complete_macros=sizes,compared_bytes=total_bytes,instruction_headers=headers,cursor_fields=2*sizes,
          baseline=dict(typed_literal=True,intended_buffers_unchanged=True,copied_other_buffer=True),commands=commands,artifacts=artifacts))
        print(f'{arch}: {sizes} complete TRANSFERDATA macros/{total_bytes} bytes/{headers} headers/{2*sizes} cursor fields match Lean',flush=True)
    (ROOT/'validation/transfer.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
