"""M13 positive copy contract: typed published baseline, repaired live imm32."""
from datetime import date
import hashlib,json,os,shutil
from pathlib import Path
from audit_encoding import coff
from generate_input_operand import generate,ROOT
from lean_export import lean_command
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def execute_arch(arch):
 folder=ROOT/"validation/.build/input_operand"/arch;fixtures=generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env["PATH"]);assert value,name;return value
 asm=[tool("ml64.exe" if arch=="x64" else "ml.exe"),"/nologo","/c","/I"+str(ROOT/"smcTuring"),"/Fo"+str(folder/"input.obj"),"/Fl"+str(folder/"input.lst")]
 asm += ["/DX64"] if arch=="x64" else ["/safeseh"]
 asm += [str(folder/"input.asm")]
 commands=[asm,[tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/I"+str(folder),"/c",str(ROOT/"validation/input_operand_native.cpp"),"/Fo"+str(folder/"harness.obj")],
   [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"input.exe"),str(folder/"input.obj"),str(folder/"harness.obj")]]
 (folder/"build.log").write_text("".join(run(command,folder,env) for command in commands),encoding="utf-8")
 output=run([str(folder/"input.exe")],folder,env);assert "PASS 6400 typed-original and 6400 corrected cases" in output,output
 (folder/"run.log").write_text(output,encoding="utf-8");print(output.strip(),flush=True)
 project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip();binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
 export_env=dict(env);export_env["PATH"]=str(binary)+os.pathsep+export_env["PATH"]
 export_env["SMCTURING_INPUT_SITES"]=str(folder/"input-packets.json");export_env["SMCTURING_INPUT_ARCH"]=arch
 reference=json.loads(run(lean_command(project,binary,["--run","ExportInputOperand.lean"]),project,export_env))
 packets=json.loads((folder/"input-packets.json").read_text());assert len(reference)==len(packets)==2
 code,symbols,relocations=coff(folder/"input.obj",arch);section,targets=relocation_targets(folder/"input.obj",arch)
 compared=0;checked=0;intervals=[]
 for actual,formal,fixture in zip(packets,reference,fixtures):
  assert actual["sites"]==formal["sites"] and actual["corrected"]==formal["corrected"]==fixture["corrected"]
  assert len(actual["packets"])==len(formal["packets"])==6
  assert len(formal["admissible"])==9 and all(formal["admissible"])
  assert formal["source_field"]==actual["sites"]["source"]+(6 if fixture["corrected"] else 0)
  assert formal["target_field"]==actual["sites"]["target"]+3
  base=actual["sites"]["start"]-symbols[fixture["names"]["Start"]]
  assert formal["end"]==symbols[fixture["names"]["Stop"]]+base
  mapping={"first":"Start","second":"Second","third":"Third","source":"Source","target":"Target","compare":"Compare"}
  for original,encoded in zip(actual["packets"],formal["packets"]):
   assert original["name"]==encoded["name"] and original["pc"]==encoded["pc"] and original["bytes"]==encoded["bytes"],(arch,original,encoded)
   name=encoded["name"];position=symbols[fixture["names"][mapping[name]]];assert original["pc"]==position+base
   expected=bytearray(encoded["bytes"]);local={}
   for payload in encoded["payloads"]:
    offset=payload["offset"];target=targets[position+offset];kind=payload["relocation"]
    assert target["kind"]==kind and target["section"]==section
    expected[offset:offset+4]=((payload["target"]-base-target["value"])%(1<<32)).to_bytes(4,"little")
    local[offset]=kind;checked+=1
   assert {offset-position:kind for offset,kind in relocations.items() if position<=offset<position+len(expected)}==local
   assert bytes(expected)==code[position:position+len(expected)],(arch,name,expected.hex(),code[position:position+len(expected)].hex())
   intervals.append((original["pc"],original["pc"]+len(expected)));compared+=len(expected)
 ordered=sorted(intervals);assert all(a[1]<=b[0] for a,b in zip(ordered,ordered[1:]))
 assert checked==10 and compared==(88 if arch=="x86" else 90)
 above_dword = all(row["sites"]["start"]>=(1<<32) and row["source_field"]>=(1<<32) and row["target_field"]>=(1<<32) for row in reference)
 if arch=="x64":assert above_dword
 (folder/"lean-packets.json").write_text(json.dumps(reference,indent=2)+"\n",encoding="utf-8")
 (folder/"native.disasm.txt").write_text(run([tool("dumpbin.exe"),"/DISASM",str(folder/"input.obj")],folder,env),encoding="utf-8")
 files=["input.asm","input.hpp","manifest.json","input.obj","input.lst","harness.obj","input.exe","build.log","run.log","input-packets.json","lean-packets.json","native.disasm.txt"]
 return dict(architecture=arch,passed=True,typed_original_executions=6400,corrected_executions=6400,source_offset=6,target_offset=3,
   complete_packets=12,compared_bytes=compared,address_relocations=checked,admissible_checks=9,
   actual_natural_addresses_above_dword=above_dword,
   current_symbol_low_ax_zero_extension_gpr_stack_flags_endpoint_exterior_reuse=True,
   commands=commands,artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),"/"):digest(folder/name) for name in files})

def main():
 runs=[execute_arch(arch) for arch in ["x86","x64"]]
 lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"));assert lean["passed"] and lean["input_operand_checked"] and lean["dword_copy_checked"]
 sources=["validation/generate_input_operand.py","validation/run_input_operand.py","validation/input_operand_native.cpp","validation/generate_terminal.py","validation/run_terminal.py",
   "validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/audit_encoding.py","smcTuring/pure_smc.inc","validation/.cache/morse-2018.pdf",
   "lean/ExportInputOperand.lean","lean/SmcTuring/Appendix/InputOperand.lean","lean/SmcTuring/Appendix/InputDword.lean"]+[f"lean/SmcTuring/Native/{name}.lean" for name in ["DwordCode","DwordLayout","DwordEffects","DwordImage"]]
 pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
 for name in sources:
  if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,complete_loaded_and_object_packets_checked=True,
   proofs=lean["checked_input_operand_declarations"],dword_proofs=lean["checked_dword_copy_declarations"],
   dword_execution_checked=True,dword_theorem="SmcTuring.Appendix.InputDword.copy_correct",dword_purity_theorem="SmcTuring.Appendix.InputDword.copy_pure",
   lean_audit_sha256=digest(ROOT/"validation/lean.json"),runs=runs,
   theorem="SmcTuring.Appendix.InputOperand.copy_correct",purity_theorem="SmcTuring.Appendix.InputOperand.copy_pure",
   scope="M13 adds only IMMOFFS to the source operand. Both-mode universal actual current-byte DWORD helper execution, current-symbol-derived target encoding, four-byte effect/purity/source/code-header/exterior frame, EAX restoration and correct long-mode RAX zero extension are checked. Future fetches derive from the initial code image; natural long-mode addresses retain all bits. Nine proved-equivalent static capacity/separation/RIP checks and all native loaded/COFF packets match the actual model. Full Listing 8 and physical ISA/configuration/fetch remain separate.",
   sources={name:digest(ROOT/name) for name in sources})
 (ROOT/"validation/input_operand.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
 print("Input operand: PASS 15 local + 77 both-mode DWORD proofs; x86/x64 each 6400 corrected + 6400 typed-original cases/12 full packets/10 relocations",flush=True)
if __name__=="__main__":main()
