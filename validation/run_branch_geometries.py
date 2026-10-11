"""Verify all 24 disjoint x86 branch region orders against actual Lean bytes."""
from datetime import date
import hashlib,json,os,re,shutil
from pathlib import Path
from audit_encoding import coff
from generate_branch_geometries import generate,ORDERS
from lean_export import lean_command
from run_branch import inspect,PAPER_SHA256
from run_defaddr import vc_environment,run

ROOT=Path(__file__).resolve().parents[1]
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    folder=ROOT/"validation/.build/branch_geometries"
    fixtures=generate(folder);assert len(fixtures)==288
    environment=vc_environment("x86")
    def tool(name):
        result=shutil.which(name,path=environment["PATH"]);assert result,name;return result
    commands=[
      [tool("ml.exe"),"/nologo","/c","/safeseh","/Fo"+str(folder/"branch.obj"),"/Fl"+str(folder/"branch.lst"),str(folder/"branch.asm")],
      [tool("cl.exe"),"/nologo","/std:c++17","/O2","/EHsc","/W4","/WX","/c","/I"+str(folder),str(folder/"harness.cpp"),"/Fo"+str(folder/"harness.obj")],
      [tool("link.exe"),"/nologo","/SECTION:.text,ERW","/CETCOMPAT:NO","/OUT:"+str(folder/"branch.exe"),str(folder/"harness.obj"),str(folder/"branch.obj")]]
    (folder/"build.log").write_text("".join(run(command,folder,environment) for command in commands),encoding="utf-8")
    batches=[];outputs=[]
    for geometry,order in enumerate(ORDERS):
        command=[str(folder/"branch.exe"),str(geometry)]
        output=run(command,folder,environment);outputs.append(output)
        matches=re.findall(r"^BRANCH (\S+): PASS (\d+) cases, (\d+) taken, (\d+) fallthrough$",output,re.M)
        chosen=fixtures[12*geometry:12*(geometry+1)]
        assert [row[0] for row in matches]==[f["name"] for f in chosen]
        assert all(int(total)==int(taken)+int(fall)==6200 and int(taken)>0 and int(fall)>0 for _,total,taken,fall in matches)
        assert "BRANCH x86: PASS 74400 cases" in output
        batches.append(dict(geometry=geometry,order=list(order),executions=74400,command=command,
          cases=[dict(name=name,executions=int(total),taken=int(taken),fallthrough=int(fall)) for name,total,taken,fall in matches]))
        print("Branch geometry "+str(geometry)+": PASS 74400 cases; "+"/".join(order),flush=True)
    (folder/"run.log").write_text("".join(outputs),encoding="utf-8")
    project=ROOT/"lean";chain=(project/"lean-toolchain").read_text().strip()
    binary=project/".elan/toolchains"/chain.replace("/","--").replace(":","---")/"bin"
    export_environment=dict(environment);export_environment["PATH"]=str(binary)+os.pathsep+export_environment["PATH"]
    shapes=json.loads(run(lean_command(project,binary,["ExportBranchEncoding.lean"]),project,export_environment))
    layouts=json.loads(run(lean_command(project,binary,["ExportBranchLayout.lean"]),project,export_environment))
    _,symbols,_=coff(folder/"branch.obj","x86")
    sites=[dict(signed=f["signed"],relation=f["relation"],stack=symbols[f["labels"]["Stack"]],
      start=symbols[f["labels"]["Start"]],taken=symbols[f["labels"]["Taken"]],data=symbols[f["labels"]["X"]]) for f in fixtures]
    (folder/"sites.json").write_text(json.dumps(sites,indent=2)+"\n",encoding="utf-8")
    export_environment["SMCTURING_BRANCH_SITES"]=str(folder/"sites.json")
    spaced=json.loads(run(lean_command(project,binary,["ExportBranchSpaced.lean"]),project,export_environment))
    assert len(spaced)==288 and all(row["valid"] and len(row["admissible_checks"])==10 and all(row["admissible_checks"]) for row in spaced)
    for fixture,row in zip(fixtures,spaced):
        physical={"stack":row["sites"]["stack"],"core":row["sites"]["start"],"taken":row["sites"]["taken"],"data":row["sites"]["data"]}
        assert sorted(physical,key=physical.get)==fixture["geometry_order"]
    results=[]
    for geometry in range(24):
        results+=inspect(folder,fixtures[12*geometry:12*(geometry+1)],shapes,layouts,spaced[12*geometry:12*(geometry+1)])
    assert len(results)==288
    assert sum(row["backward"] for row in spaced)==144
    assert sum(row["ordered"] for row in spaced)==12
    for name,value in [("shapes",shapes),("layouts",layouts),("spaced",spaced),("comparison",results)]:
        (folder/(name+".json")).write_text(json.dumps(value,indent=2)+"\n",encoding="utf-8")
    lean=json.loads((ROOT/"validation/lean.json").read_text(encoding="utf-8"))
    assert lean["passed"] and lean["appendix_branch_geometry_checked"]
    sources=["validation/generate_branch_geometries.py","validation/run_branch_geometries.py","validation/generate_branch.py",
      "validation/branch_native.cpp","validation/run_branch.py","validation/run_defaddr.py","validation/audit_encoding.py",
      "validation/lean_build.py",'validation/lean_export.py','validation/module_artifacts.py','validation/memory_budget.py','validation/limited_run.py',"validation/.cache/morse-2018.pdf",
      "lean/ExportBranchEncoding.lean","lean/ExportBranchLayout.lean","lean/ExportBranchSpaced.lean"]
    sources += ["lean/SmcTuring/Appendix/"+name+".lean" for name in
      ["ByteRegions","SpacedLayout","SpacedPrefix","SpacedControl","SpacedPaths","SpacedWhole"]]
    assert digest(ROOT/"validation/.cache/morse-2018.pdf")==PAPER_SHA256
    pinned={name.replace(chr(92),"/"):value for name,value in lean["sources"].items()}
    for name in sources:
        if name.startswith("lean/"):assert digest(ROOT/name)==pinned[name]
    files=["branch.asm","branch.hpp","manifest.json","branch.obj","branch.lst","harness.cpp","harness.obj","branch.exe",
      "build.log","run.log","shapes.json","layouts.json","sites.json","spaced.json","comparison.json"]
    report=dict(as_of=date.today().isoformat(),passed=True,architecture="x86",region_orders=24,relation_modes=12,
      layouts=288,backward_layouts=144,executions=1785600,original_pure_instruction_order=True,
      current_byte_whole_execution_proof=True,ten_static_checks=True,
      pure_packets=sum(r["instruction_headers"] for r in results),owner_fields=7*len(results),
      address_relocations=sum(r["checked_relocations"] for r in results),batches=batches,comparison=results,
      proofs=lean["checked_appendix_branch_geometry_declarations"],lean_audit_sha256=digest(ROOT/"validation/lean.json"),
      scope="All disjoint finite x86 region orders and backward/forward targets: original-image current-byte trace, actual PC, input/EAX/ESP/CF, code-owned writes and exact exterior-byte frame; physical ISA/configuration/fetch remains E05/A01.",
      commands=commands,sources={name:digest(ROOT/name) for name in sources},
      artifacts={str((folder/name).relative_to(ROOT)).replace("\\","/"):digest(folder/name) for name in files})
    (ROOT/"validation/branch_geometries.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print("Branch geometries: PASS 24 orders/288 layouts/144 backward targets/1785600 executions; "+str(report["pure_packets"])+" complete packets",flush=True)

if __name__=="__main__":main()
