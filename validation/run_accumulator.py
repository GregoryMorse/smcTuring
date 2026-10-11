"""Positive printed Listing 9 and terminal native/full-packet regression."""
from datetime import date
import hashlib,json,os,shutil
from pathlib import Path
from audit_encoding import coff
from generate_accumulator import generate,ROOT
from lean_export import lean_command
from run_defaddr import vc_environment,run
from run_terminal import relocation_targets

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def execute_arch(arch):
 folder=ROOT/"validation/.build/accumulator"/arch;fixtures=generate(folder,arch);env=vc_environment(arch)
 def tool(name):
  value=shutil.which(name,path=env["PATH"]);assert value,name;return value
 asm=[tool("ml64.exe" if arch=="x64" else "ml.exe"),"/nologo","/c","/I"+str(ROOT/"smcTuring"),"/Fo"+str(folder/"accumulator.obj"),"/Fl"+str(folder/"accumulator.lst")]
 asm += ["/DX64"] if arch=="x64" else ["/safeseh"]
 asm += [str(folder/"accumulator.asm")]
 commands=[asm,[tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/I"+str(folder),"/c",str(ROOT/"validation/accumulator_native.cpp"),"/Fo"+str(folder/"harness.obj")],
   [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"accumulator.exe"),str(folder/"accumulator.obj"),str(folder/"harness.obj")]]
 (folder/"build.log").write_text("".join(run(command,folder,env) for command in commands),encoding="utf-8")
 output=run([str(folder/"accumulator.exe")],folder,env);assert "PASS 38400 executions; 6 owner orders" in output,output
 (folder/"run.log").write_text(output,encoding="utf-8");print(output.strip(),flush=True)
 project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip();binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
 export_env=dict(env);export_env["PATH"]=str(binary)+os.pathsep+export_env["PATH"]
 export_env["SMCTURING_ACCUMULATOR_SITES"]=str(folder/"accumulator-packets.json");export_env["SMCTURING_ACCUMULATOR_ARCH"]=arch
 reference=json.loads(run(lean_command(project,binary,["--run","ExportAccumulator.lean"]),project,export_env))
 packets=json.loads((folder/"accumulator-packets.json").read_text());assert len(reference)==len(packets)==6
 code,symbols,relocations=coff(folder/"accumulator.obj",arch);section,targets=relocation_targets(folder/"accumulator.obj",arch)
 compared=0;checked_relocations=0;control=0;owners=0
 for actual,formal,fixture in zip(packets,reference,fixtures):
  assert len(formal["checks"])==9 and all(formal["checks"]) and formal["save_marker_apart"]
  assert actual["sites"]==formal["sites"] and len(actual["packets"])==len(formal["packets"])==12
  base=actual["sites"]["prologue"]-symbols[fixture["names"]["Prologue"]]
  object_name={"save":"Prologue","bodyFirst":"BodyFirst","bodySecond":"BodySecond","bodyStore":"BodyStore","first":"Epilogue","second":"Second","third":"Third","terminal":"Marker",
    "saveOwner":"SaveOwner","pointerOwner":"PointerOwner","bodyOwner":"BodyOwner","outputOwner":"OutputOwner"}
  assert formal["marker"]==symbols[fixture["names"]["Marker"]]+base
  assert formal["end"]==symbols[fixture["names"]["MarkerEnd"]]+base
  intervals=[]
  for original,encoded in zip(actual["packets"],formal["packets"]):
   assert original["name"]==encoded["name"] and original["pc"]==encoded["pc"] and original["bytes"]==encoded["bytes"],(arch,original,encoded)
   name=encoded["name"];position=symbols[fixture["names"][object_name[name]]];assert original["pc"]==position+base
   expected=bytearray(encoded["bytes"]);local={}
   for payload in encoded["payloads"]:
    offset=payload["offset"];width=payload["width"];kind=payload["relocation"];target=targets[position+offset]
    assert target["kind"]==kind and target["section"]==section
    expected[offset:offset+width]=((payload["target"]-base-target["value"])%(1<<(8*width))).to_bytes(width,"little")
    local[offset]=kind;checked_relocations+=1
   assert {offset-position:kind for offset,kind in relocations.items() if position<=offset<position+len(expected)}==local
   assert bytes(expected)==code[position:position+len(expected)],(arch,name,expected.hex(),code[position:position+len(expected)].hex())
   intervals.append((original["pc"],original["pc"]+len(expected)));compared+=len(expected)
   if name.endswith("Owner"):owners+=1
   else:control+=1
  sorted_intervals=sorted(intervals);assert all(a[1]<=b[0] for a,b in zip(sorted_intervals,sorted_intervals[1:]))
  for field in ["save","pointer","body","output"]:
   owner=next(p for p in formal["packets"] if p["name"]==field+"Owner")
   assert formal["sites"][field]==owner["pc"]+(1 if arch=="x86" else 2)
   assert len(owner["bytes"])-(1 if arch=="x86" else 2)==(4 if arch=="x86" else 8)
 assert control==48 and owners==24 and checked_relocations==54
 assert compared==(408 if arch=="x86" else 594)
 (folder/"lean-packets.json").write_text(json.dumps(reference,indent=2)+"\n",encoding="utf-8")
 (folder/"native.disasm.txt").write_text(run([tool("dumpbin.exe"),"/DISASM",str(folder/"accumulator.obj")],folder,env),encoding="utf-8")
 files=["accumulator.asm","accumulator.hpp","manifest.json","accumulator.obj","accumulator.lst","harness.obj","accumulator.exe","build.log","run.log","accumulator-packets.json","lean-packets.json","native.disasm.txt"]
 return dict(architecture=arch,passed=True,executions=38400,layouts=6,control_packets=control,owner_packets=owners,compared_bytes=compared,address_relocations=checked_relocations,
   full_gpr_stack_status_flags_outputs_endpoint_code_frame_reuse=True,original_listing9_instruction_order=True,complete_word_fields=True,
   commands=commands,artifacts={str((folder/name).relative_to(ROOT)).replace(chr(92),"/"):digest(folder/name) for name in files})

def main():
 runs=[execute_arch(arch) for arch in ["x86","x64"]]
 lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"));assert lean["passed"] and lean["accumulator_finalization_checked"]
 sources=["validation/generate_accumulator.py","validation/run_accumulator.py","validation/accumulator_native.cpp","validation/generate_terminal.py","validation/run_terminal.py",
   "validation/run_defaddr.py","validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/audit_encoding.py","smcTuring/pure_smc.inc","smcTuring/terminal_smc.inc","validation/.cache/morse-2018.pdf",
   "lean/ExportAccumulator.lean"]+ ["lean/SmcTuring/Native/"+name+".lean" for name in ["AccumulatorLayout","AccumulatorEffects","AccumulatorImage","AccumulatorFinalization","TerminalMarker","DwordStore"]]
 pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
 for name in sources:
  if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
 report=dict(as_of=date.today().isoformat(),passed=True,actual_lean_codec_checked=True,complete_loaded_and_object_packets_checked=True,
   proofs=lean["checked_accumulator_finalization_declarations"],lean_audit_sha256=digest(ROOT/"validation/lean.json"),runs=runs,
   theorem="SmcTuring.Native.AccumulatorFinalization.surround",purity_theorem="SmcTuring.Native.AccumulatorFinalization.surrounding_pure",
   scope="Printed four-instruction Listing 9 order on code-owned complete full-width fields, current-byte traces, original pointer initializer, reusable AX/SP/CF/save/pointer/output frames and corrected terminal composition. Six concrete full-width MOFFS storage-owner orders per architecture; complete Listing 8 body and optimized DEFDATA32/native x64 half placement remain separate.",
   sources={name:digest(ROOT/name) for name in sources})
 (ROOT/"validation/accumulator.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
 print("Accumulator finalization: PASS 49 proofs; x86/x64 each 38400 cases/6 layouts/72 full packets/54 relocations",flush=True)
if __name__=="__main__":main()
