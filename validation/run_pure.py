"""Build and retest the complete repaired SMC MOV kernel on x86 and x64."""
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
from export_kernel import export
from generate_pure import generate
from pure_suite import write_suite
from run_defaddr import vc_environment, run

ROOT = Path(__file__).resolve().parents[1]

def main():
    kernel = export()
    sources = ["validation/export_kernel.py","lean/ExportKernel.lean","validation/generate_pure.py",
               "validation/pure_native.cpp","validation/pure_suite.py","validation/run_pure.py",
               "validation/run_defaddr.py","validation/kernel.json","validation/lean_build.py","validation/lean_export.py","validation/module_artifacts.py",
               "validation/memory_budget.py","validation/limited_run.py","lean/lakefile.proof.toml"]
    report = {"as_of":date.today().isoformat(),"purpose":"Complete repaired SMC kernel differential native validation",
              "sources":{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sources},
              "processor":os.environ.get("PROCESSOR_IDENTIFIER"),"runs":[]}
    lean_evidence = json.loads((ROOT/"validation/lean.json").read_text())
    assert lean_evidence["passed"]
    for name, expected in lean_evidence["sources"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected, "Stale Lean evidence: "+name
    report["lean_audit_sha256"] = hashlib.sha256((ROOT/"validation/lean.json").read_bytes()).hexdigest()
    report["lean_source_hashes"] = lean_evidence["sources"]
    for architecture in ["x86","x64"]:
        folder = ROOT / "validation/.build/pure" / architecture
        layout = generate(folder, architecture, kernel["instructions"])
        scenarios = write_suite(folder / "suite.bin", kernel["instructions"])
        env = vc_environment(architecture)
        def tool(name):
            found = shutil.which(name, path=env["PATH"])
            if not found: raise RuntimeError("Missing " + name)
            return found
        assemble = [tool("ml64.exe" if architecture=="x64" else "ml.exe"),"/nologo","/c",
                    "/Fo"+str(folder/"pure.obj"),"/Fl"+str(folder/"pure.lst")]
        if architecture=="x86": assemble.append("/safeseh")
        assemble.append(str(folder/"pure.asm"))
        compile_cpp = [tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/c",
                       "/I"+str(folder),str(ROOT/"validation/pure_native.cpp"),"/Fo"+str(folder/"harness.obj")]
        link = [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"pure.exe"),
                str(folder/"harness.obj"),str(folder/"pure.obj")]
        build = run(assemble,folder,env)+run(compile_cpp,folder,env)+run(link,folder,env)
        (folder/"build.log").write_text(build)
        output = run([str(folder/"pure.exe"),str(folder/"suite.bin")],folder,env)
        print(output.strip(),flush=True)
        match = re.search(r"PASS (\d+) cases, (\d+) kernel passes, (\d+) terminal cases, (\d+) closed loops",output)
        assert match and int(match[1])==len(scenarios), output
        disassembly = run([tool("dumpbin.exe"),"/DISASM",str(folder/"pure.obj")],folder,env)
        (folder/"pure.disasm.txt").write_text(disassembly)
        (folder/"run.log").write_text(output)
        report["runs"].append({"architecture":architecture,"passed":True,"cases":int(match[1]),"kernel_passes":int(match[2]),
                               "terminal_cases":int(match[3]),"closed_loop_cases":int(match[4]),"output":output,"scenarios":scenarios,
                               "layout":layout,"commands":[assemble,compile_cpp,link],
                               "generated_assembly_sha256":hashlib.sha256((folder/"pure.asm").read_bytes()).hexdigest(),
                               "executable_sha256":hashlib.sha256((folder/"pure.exe").read_bytes()).hexdigest(),
                               "disassembly_sha256":hashlib.sha256(disassembly.encode()).hexdigest()})
        (ROOT/"validation/pure.json").write_text(json.dumps(report,indent=2)+"\n")

if __name__ == "__main__": main()
