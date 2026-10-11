"""Positive DEFDATA32 live scalar owner, full packets and COFF targets."""
from datetime import date
import hashlib,json,os,shutil,subprocess
from pathlib import Path
from audit_encoding import coff
from generate_dword_owner import generate,ROOT
from lean_export import lean_command
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def execute_arch(arch):
 folder=ROOT/"validation/.build/dword_owner"/arch;generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env["PATH"]);assert value,name;return value
 asm=[tool("ml64.exe" if arch=="x64" else "ml.exe"),"/nologo","/c","/I"+str(ROOT/"smcTuring"),"/Fo"+str(folder/"owner.obj"),"/Fl"+str(folder/"owner.lst")]
 asm += ["/DX64"] if arch=="x64" else ["/safeseh"]
 asm += [str(folder/"owner.asm")]
 commands=[asm,[tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/I"+str(folder),"/c",str(ROOT/"validation/dword_owner_native.cpp"),"/Fo"+str(folder/"harness.obj")],
  [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"owner.exe"),str(folder/"owner.obj"),str(folder/"harness.obj")]]
 (folder/"build.log").write_text("".join(run(command,folder,env) for command in commands),encoding="utf-8")
 output=run([str(folder/"owner.exe")],folder,env);assert "PASS 6400 cases" in output,output
 (folder/"run.log").write_text(output,encoding="utf-8");print(output.strip(),flush=True)
 project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip();binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
 export_env=dict(env);export_env["PATH"]=str(binary)+os.pathsep+export_env["PATH"]
 export_env["SMCTURING_OWNER_SITES"]=str(folder/"owner-packets.json");export_env["SMCTURING_OWNER_ARCH"]=arch
 exported=subprocess.run(lean_command(project,binary,["--run","ExportDwordOwner.lean"]),cwd=project,env=export_env,capture_output=True,text=True,errors="replace",timeout=600)
 assert exported.returncode==0,exported.stdout+exported.stderr
 reference=json.loads(exported.stdout)
 actual=json.loads((folder/"owner-packets.json").read_text());assert actual["pc"]==reference["pc"] and actual["endpoint"]==reference["endpoint"]==actual["pc"]+10
 assert reference["width"]==4 and reference["field"]==actual["pc"]+6
 assert actual["initial"]==reference["initial"] and actual["live"]==reference["live"] and len(actual["live"])==40
 assert all(len(row["bytes"])==10 for row in [actual["initial"]]+actual["live"])
 code,symbols,relocations=coff(folder/"owner.obj",arch);section,targets=relocation_targets(folder/"owner.obj",arch)
 position=symbols["OwnerMarker"];base=actual["pc"]-position
 assert symbols["OwnerMarkerEnd"]==position+10 and reference["relocation"]==(6 if arch=="x86" else 8)
 target=targets[position+2];assert target["kind"]==reference["relocation"] and target["section"]==section
 expected=bytearray(reference["initial"]["bytes"]);expected[2:6]=((reference["field"]-base-target["value"])%(1<<32)).to_bytes(4,"little")
 assert bytes(expected)==code[position:position+10]
 assert {offset-position:kind for offset,kind in relocations.items() if position<=offset<position+10}=={2:reference["relocation"]}
 (folder/"lean-packets.json").write_text(json.dumps(reference,indent=2)+"\n",encoding="utf-8")
 (folder/"native.disasm.txt").write_text(run([tool("dumpbin.exe"),"/DISASM",str(folder/"owner.obj")],folder,env),encoding="utf-8")
 files=["owner.asm","owner.hpp","owner.obj","owner.lst","harness.obj","owner.exe","build.log","run.log","owner-packets.json","lean-packets.json","native.disasm.txt"]
 return dict(architecture=arch,passed=True,executions=6400,live_words=40,initial_packet=1,complete_live_packets=40,compared_bytes=410,address_relocations=1,
   own_immediate_offset=6,operand_width=4,instruction_bytes=10,full_ax_gpr_stack_flags_endpoint_live_symbol_whole_packet_reuse=True,
   commands=commands,artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),"/"):digest(folder/name) for name in files})

def main():
 runs=[execute_arch(arch) for arch in ["x86","x64"]]
 lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"));assert lean["passed"] and lean["dword_owner_checked"]
 sources=["validation/generate_dword_owner.py","validation/run_dword_owner.py","validation/dword_owner_native.cpp","validation/generate_terminal.py","validation/run_terminal.py",
   "validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/audit_encoding.py","smcTuring/dword_owner_smc.inc","validation/.cache/morse-2018.pdf",
   "lean/ExportDwordOwner.lean","lean/SmcTuring/Native/DwordOwner.lean"]
 pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
 for name in sources:
  if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,complete_loaded_and_object_packets_checked=True,
   proofs=lean["checked_dword_owner_declarations"],lean_audit_sha256=digest(ROOT/"validation/lean.json"),runs=runs,
   theorem="SmcTuring.Native.DwordOwner.correct",purity_theorem="SmcTuring.Native.DwordOwner.pure",
   scope="M14 uses existing printed DEFDATA32(curtinputval,0): exact ten-byte current DWORD owner, operand at six, both-mode selected current-byte execution/full AX/SP/CF/whole-memory preservation/nonempty code-owned write. Current value and zero initializer, complete packet derivation after live operand patch, and native full GPR/status-flag/reuse frames are checked. Full Listing 8 composition remains separate.",
   sources={name:digest(ROOT/name) for name in sources})
 (ROOT/"validation/dword_owner.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
 print("DWORD owner: PASS 17 positive proofs; x86/x64 each 6400 cases/40 live full packets/initial zero packet/one relocation",flush=True)
if __name__=="__main__":main()
