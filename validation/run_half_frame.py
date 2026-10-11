"""Finite native regression of corresponding-half USEWORD32 and unary NOT.
The x64 fixture follows the printed two-half macros; x86 exercises two
instances of each 32-bit primitive (the printed x86 OP64 emits only one half).

Observe low AX, CF, all four code operand words and every non-target code byte.
On x64, the EAX exchanges clear upper RAX; NOT leaves the full RAX unchanged.
"""
from pathlib import Path
import hashlib,json,os,re,shutil
from run_defaddr import vc_environment,run
ROOT=Path(__file__).resolve().parents[1]
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    lean_path=ROOT/'validation/lean.json'
    lean=json.loads(lean_path.read_text(encoding='utf-8'))
    proof=ROOT/'lean/SmcTuring/X64/HalfFrame.lean'
    assert lean['sources'][str(proof.relative_to(ROOT))]==digest(proof),'Refresh the Lean proof audit first'
    names=[item['name'] for item in lean['declarations'] if item['name'].startswith('SmcTuring.X64.HalfFrame.')]
    assert len(names)==28 and 'SmcTuring.X64.HalfFrame.split_correct' in names
    sources=['validation/run_half_frame.py','validation/half_frame_native.asm',
             'validation/half_frame_native.cpp','validation/run_defaddr.py','lean/SmcTuring/X64/HalfFrame.lean']
    report=dict(as_of='2026-10-05',passed=True,scope='Finite corresponding-half regression: printed x64 two-half pattern and x86 paired primitives; word-model contract, not physical fetch refinement',
                sources={name:digest(ROOT/name) for name in sources},lean_audit_sha256=digest(lean_path),proofs=names,runs=[])
    for arch in ['x86','x64']:
        folder=ROOT/'validation/.build/half-frame'/arch;folder.mkdir(parents=True,exist_ok=True)
        env=vc_environment(arch)
        def tool(name):
            found=shutil.which(name,path=env['PATH']);assert found,name;return found
        assemble=[tool('ml64.exe' if arch=='x64' else 'ml.exe'),'/nologo','/c','/Fo'+str(folder/'native.obj'),'/Fl'+str(folder/'native.lst')]
        if arch=='x64': assemble.append('/DX64')
        else: assemble.append('/safeseh')
        assemble.append(str(ROOT/'validation/half_frame_native.asm'))
        compile_cpp=[tool('cl.exe'),'/nologo','/std:c++17','/O2','/EHsc','/W4','/WX','/c',str(ROOT/'validation/half_frame_native.cpp'),'/Fo'+str(folder/'harness.obj')]
        link=[tool('link.exe'),'/nologo','/SECTION:.text,ERW','/CETCOMPAT:NO','/OUT:'+str(folder/'half-frame.exe'),str(folder/'harness.obj'),str(folder/'native.obj')]
        (folder/'build.log').write_text(''.join(run(cmd,folder,env) for cmd in [assemble,compile_cpp,link]),encoding='utf-8')
        output=run([str(folder/'half-frame.exe')],folder,env)
        assert f'Half-frame {32 if arch=="x86" else 64}-bit: PASS 17290 cases' in output,output
        (folder/'run.log').write_text(output,encoding='utf-8')
        (folder/'native.disasm.txt').write_text(run([tool('dumpbin.exe'),'/DISASM',str(folder/'native.obj')],folder,env),encoding='utf-8')
        report['runs'].append(dict(architecture=arch,passed=True,cases=17290,operations=5,incoming_carry_cases=2,output=output,
                                  commands=[assemble,compile_cpp,link],artifacts={str(path.relative_to(ROOT)):digest(path) for path in
                                  [folder/'native.obj',folder/'native.lst',folder/'native.disasm.txt',folder/'half-frame.exe',folder/'run.log']}))
        print(output.strip(),flush=True)
    (ROOT/'validation/half-frame.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__': main()
