"""Package public proof sources and runner; exclude private and build files."""
import json,tarfile
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
files=list((ROOT/"lean").glob("*.lean"))+list((ROOT/"lean/SmcTuring").rglob("*.lean"))
files += [ROOT/name for name in ["lean/lean-toolchain","lean/lakefile.toml",
 "lean/lakefile.proof.toml","lean/lake-manifest.json","validation/remote_build.py",
 "validation/remote_artifacts.py","AGENTS.md"]]
destination=ROOT/"validation/.build/remote-sources.tar"
with tarfile.open(destination,"w") as archive:
 for path in sorted(files):archive.add(path,arcname=str(path.relative_to(ROOT)),recursive=False)
print("Source bundle: "+str(len(files))+" files; "+str(destination.stat().st_size)+" bytes")
