"""Positive M12 terminal marker proof/native packet and reentry regression."""
from datetime import date
import hashlib,json,os,re,shutil,struct
from pathlib import Path
from audit_encoding import coff
from generate_terminal import generate,ROOT
from lean_export import lean_command
from run_defaddr import vc_environment,run

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def relocation_targets(path,arch):
    data=path.read_bytes()
    machine,count,_,symbol_start,symbol_count,optional_size,_=struct.unpack_from("<HHIIIHH",data)
    assert machine=={"x86":0x14c,"x64":0x8664}[arch]
    sections=[struct.unpack_from("<8sIIIIIIHHI",data,20+optional_size+40*i) for i in range(count)]
    chosen=[i for i,section in enumerate(sections) if section[0].rstrip(b"\0")==b".text$mn"]
    assert len(chosen)==1
    number=chosen[0]+1;section=sections[chosen[0]];symbols={};index=0
    while index<symbol_count:
        _,value,owner,_,_,aux=struct.unpack_from("<8sIhHBB",data,symbol_start+index*18)
        symbols[index]=(value,owner);index+=1+aux
    targets={}
    for index in range(section[7]):
        position,symbol,kind=struct.unpack_from("<IIH",data,section[5]+10*index)
        value,owner=symbols[symbol]
        targets[position]=dict(value=value,section=owner,kind=kind)
    return number,targets

def execute_arch(arch):
    folder=ROOT/"validation/.build/terminal"/arch
    generate(folder,arch);env=vc_environment(arch)
    def tool(name):
        value=shutil.which(name,path=env["PATH"]);assert value,name;return value
    asm=[tool("ml64.exe" if arch=="x64" else "ml.exe"),"/nologo","/c","/I"+str(ROOT/"smcTuring"),"/Fo"+str(folder/"terminal.obj"),"/Fl"+str(folder/"terminal.lst")]
    if arch=="x86":asm+=["/safeseh"]
    asm+=[str(folder/"terminal.asm")]
    commands=[asm,[tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/I"+str(folder),"/c",str(ROOT/"validation/terminal_native.cpp"),"/Fo"+str(folder/"harness.obj")],
      [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"terminal.exe"),str(folder/"harness.obj"),str(folder/"terminal.obj")]]
    (folder/"build.log").write_text("".join(run(command,folder,env) for command in commands),encoding="utf-8")
    output=run([str(folder/"terminal.exe")],folder,env)
    assert "PASS 4128 typed-original and 4128 corrected cases" in output,output
    (folder/"run.log").write_text(output,encoding="utf-8");print(output.strip(),flush=True)
    project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip()
    binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
    export_env=dict(env);export_env["PATH"]=str(binary)+os.pathsep+export_env["PATH"]
    export_env["SMCTURING_TERMINAL_SITES"]=str(folder/"terminal-packets.json")
    export_env["SMCTURING_TERMINAL_ARCH"]=arch
    reference=json.loads(run(lean_command(project,binary,["--run","ExportTerminal.lean"]),project,export_env))
    packets=json.loads((folder/"terminal-packets.json").read_text())
    assert len(reference)==len(packets)==2
    code,symbols,relocations=coff(folder/"terminal.obj",arch)
    section,targets=relocation_targets(folder/"terminal.obj",arch)
    for index,(actual,formal) in enumerate(zip(packets,reference)):
        assert actual["bytes"]==formal["bytes"] and actual["pc"]==formal["pc"]
        assert formal["length"]==10 and formal["next_pc"]==actual["pc"]+10
        name=("Corrected" if index else "Literal")+"Marker";pc=symbols[name]
        assert symbols[name+"End"]==pc+10
        expected=bytearray(actual["bytes"])
        kind=6 if arch=="x86" else 8  # DIR32 or AMD64 REL32_4: four trailing immediate bytes.
        assert {position-pc:tag for position,tag in relocations.items() if pc<=position<pc+10}=={2:kind}
        target=targets[pc+2];assert target["kind"]==kind and target["section"]==section
        if arch=="x64":assert int.from_bytes(expected[2:6],"little",signed=True)==(-4 if index else -10)
        expected[2:6]=((pc+(6 if index else 0)-target["value"])%(1<<32)).to_bytes(4,"little")
        assert bytes(expected)==code[pc:pc+10],(arch,name,expected.hex(),code[pc:pc+10].hex())
    (folder/"lean-packets.json").write_text(json.dumps(reference,indent=2)+"\n",encoding="utf-8")
    (folder/"native.disasm.txt").write_text(run([tool("dumpbin.exe"),"/DISASM",str(folder/"terminal.obj")],folder,env),encoding="utf-8")
    files=["terminal.asm","terminal.hpp","terminal.obj","terminal.lst","harness.obj","terminal.exe","build.log","run.log","terminal-packets.json","lean-packets.json","native.disasm.txt"]
    return dict(architecture=arch,passed=True,typed_original_executions=4128,corrected_executions=4128,
      own_immediate_offset=6,instruction_bytes=10,full_packets=2,code_address_relocations=2,
      all_gpr_stack_status_flags_endpoint_frame_reuse=True,commands=commands,
      artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),"/"):digest(folder/name) for name in files})

def main():
    runs=[execute_arch(arch) for arch in ["x86","x64"]]
    lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"))
    assert lean["passed"] and lean["terminal_marker_checked"]
    sources=["validation/generate_terminal.py","validation/run_terminal.py","validation/terminal_native.cpp",
      "smcTuring/terminal_smc.inc","validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/audit_encoding.py",
      "lean/ExportTerminal.lean","lean/SmcTuring/Native/TerminalMarker.lean",
      "lean/SmcTuring/Native/DwordStore.lean","lean/SmcTuring/Native/ByteMemory.lean"]
    pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
    for name in sources:
        if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
    report=dict(as_of=date.today().isoformat(),passed=True,proofs=lean["checked_terminal_marker_declarations"],
      actual_lean_codec_checked=True,complete_object_and_loaded_packets_checked=True,runs=runs,
      lean_audit_sha256=digest(ROOT/"validation/lean.json"),
      theorem="SmcTuring.Native.TerminalMarker.correct",purity_theorem="SmcTuring.Native.TerminalMarker.pure",
      scope="Both selected x86/x64 current-byte DWORD stores: exact self immediate, next-PC observation, AX/SP/CF, whole memory/output/header reuse and nonempty code-owned writes. Native checks all GPRs/status flags; physical CPU/fetch refinement remains separate.",
      sources={name:digest(ROOT/name) for name in sources})
    (ROOT/"validation/terminal.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print("Terminal marker: PASS x86/x64 proof/complete-packet comparison; each 4128 typed-original + 4128 corrected executions",flush=True)
if __name__=="__main__":main()
