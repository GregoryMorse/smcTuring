"""Literal comparison: exact current packets, native oracle and seven COFF targets."""
from datetime import date
import hashlib,json,os,shutil,subprocess
from pathlib import Path
from audit_encoding import coff
from generate_dword_comparison import generate,ROOT
from lean_export import lean_command
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def execute_arch(arch):
 folder=ROOT/"validation/.build/dword_comparison"/arch;generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env["PATH"]);assert value,name;return value
 asm=[tool("ml64.exe" if arch=="x64" else "ml.exe"),"/nologo","/c","/I"+str(ROOT/"smcTuring"),"/Fo"+str(folder/"comparison.obj"),"/Fl"+str(folder/"comparison.lst")]
 asm += ["/DX64"] if arch=="x64" else ["/safeseh"]
 asm += [str(folder/"comparison.asm")]
 commands=[asm,[tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/I"+str(folder),"/c",str(ROOT/"validation/dword_comparison_native.cpp"),"/Fo"+str(folder/"harness.obj")],
  [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"comparison.exe"),str(folder/"comparison.obj"),str(folder/"harness.obj")]]
 (folder/"build.log").write_text("".join(run(command,folder,env) for command in commands),encoding="utf-8")
 output=run([str(folder/"comparison.exe")],folder,env);assert "PASS 51200 cases/1280 matches" in output,output
 (folder/"run.log").write_text(output,encoding="utf-8");print(output.strip(),flush=True)
 project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip();binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
 export_env=dict(env);export_env["PATH"]=str(binary)+os.pathsep+export_env["PATH"]
 export_env["SMCTURING_COMPARISON_SITES"]=str(folder/"comparison-packets.json");export_env["SMCTURING_COMPARISON_ARCH"]=arch
 exported=subprocess.run(lean_command(project,binary,["--run","ExportDwordComparison.lean"]),cwd=project,env=export_env,capture_output=True,text=True,errors="replace",timeout=600)
 assert exported.returncode==0,exported.stdout+exported.stderr
 reference=json.loads(exported.stdout);actual=json.loads((folder/"comparison-packets.json").read_text())
 for key in ["pc","scalar","mask","endpoint","initial","owners","live"]:assert actual[key]==reference[key],(arch,key,actual[key],reference[key])
 assert len(reference["checks"])==11 and all(reference["checks"])
 assert len(actual["live"])==40 and len(actual["initial"])==39 and all(len(row["bytes"])==39 for row in actual["live"])
 code,symbols,relocations=coff(folder/"comparison.obj",arch);section,targets=relocation_targets(folder/"comparison.obj",arch)
 start=symbols["CompareMarker"];base=actual["pc"]-start
 assert symbols["CompareMarkerEnd"]==start+39
 assert actual["scalar"]==base+symbols["CompareScalar"]+6 and actual["mask"]==base+symbols["CompareMask"]+6
 assert symbols["CompareScalarEnd"]==symbols["CompareScalar"]+10 and symbols["CompareMaskEnd"]==symbols["CompareMask"]+10
 locations=[start+offset for offset in [2,12,22,28,35]]+[symbols["CompareScalar"]+2,symbols["CompareMask"]+2]
 destinations=[actual["mask"],actual["scalar"],actual["scalar"],actual["mask"],actual["mask"],actual["scalar"],actual["mask"]]
 sections=[(start,actual["initial"]),(symbols["CompareScalar"],actual["owners"][0]),(symbols["CompareMask"],actual["owners"][1])]
 for position,packet in sections:
  expected=bytearray(packet);local={}
  for location,destination,kind in zip(locations,destinations,reference["relocations"]):
   if position<=location<position+len(packet):
    target=targets[location];assert target["kind"]==kind and target["section"]==section
    offset=location-position;expected[offset:offset+4]=((destination-base-target["value"])%(1<<32)).to_bytes(4,"little");local[offset]=kind
  assert {offset-position:kind for offset,kind in relocations.items() if position<=offset<position+len(packet)}==local
  assert bytes(expected)==code[position:position+len(packet)],(arch,position,expected.hex(),code[position:position+len(packet)].hex())
 above_dword=all(actual[key]>=(1<<32) for key in ["pc","scalar","mask"])
 assert arch!="x64" or above_dword
 (folder/"lean-packets.json").write_text(json.dumps(reference,indent=2)+"\n",encoding="utf-8")
 (folder/"native.disasm.txt").write_text(run([tool("dumpbin.exe"),"/DISASM",str(folder/"comparison.obj")],folder,env),encoding="utf-8")
 files=["comparison.asm","comparison.hpp","comparison.obj","comparison.lst","harness.obj","comparison.exe","build.log","run.log","comparison-packets.json","lean-packets.json","native.disasm.txt"]
 return dict(architecture=arch,passed=True,executions=51200,matches=1280,current_symbols=40,complete_code_images=41,owner_packets=2,compared_bytes=1619,address_relocations=7,
  static_checks=11,x64_addresses_above_4GiB=above_dword,
  full_ax_gpr_stack_flags_endpoint_scalar_mask_code_frame_reuse=True,
  commands=commands,artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),"/"):digest(folder/name) for name in files})
def main():
 runs=[execute_arch(arch) for arch in ["x86","x64"]]
 lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"));assert lean["passed"] and lean["dword_comparison_checked"]
 sources=["validation/generate_dword_comparison.py","validation/run_dword_comparison.py","validation/dword_comparison_native.cpp","validation/generate_dword_owner.py",
  "validation/generate_terminal.py","validation/run_terminal.py","validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/audit_encoding.py","smcTuring/dword_owner_smc.inc",
  "validation/.cache/morse-2018.pdf","lean/ExportDwordComparison.lean","lean/SmcTuring/Native/DwordArithmetic.lean","lean/SmcTuring/Appendix/DwordComparison.lean"]
 pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
 for name in sources:
  if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,complete_loaded_and_object_packets_checked=True,
  proofs=lean["checked_dword_comparison_declarations"],arithmetic_proofs=lean["checked_dword_arithmetic_declarations"],lean_audit_sha256=digest(ROOT/"validation/lean.json"),runs=runs,
  theorem="SmcTuring.Appendix.DwordComparison.correct",purity_theorem="SmcTuring.Appendix.DwordComparison.pure",
  scope="Packed fixture of the printed Listing 8 DWORD comparison forms reset/SUB/NEG/SBB/NOT: both modes, current 39-byte image and actual RIP instruction ends, live scalar/mask/code frame, full AX/SP/CF, exact match mask and all five code-word writes. Native GPR/status flags/reuse supplement the selected model. The printed body interleaves the separately proved input-copy/scalar-owner instructions between reset and SUB; that composition, the full transition body and input cursor exchanges remain separate.",
  sources={name:digest(ROOT/name) for name in sources})
 (ROOT/"validation/dword_comparison.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
 print("DWORD comparison: PASS both modes each 51200 cases/1280 matches/41 full images/two owners/seven relocations/11 proved checks",flush=True)
if __name__=="__main__":main()
