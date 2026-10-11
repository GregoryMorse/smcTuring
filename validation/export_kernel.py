"""Export the actual checked Lean kernel; do not duplicate its MOV program."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
from lean_export import lean_command

ROOT = Path(__file__).resolve().parents[1]

def export():
    project = ROOT / "lean"
    version = (project / "lean-toolchain").read_text().strip()
    binary = project / ".elan/toolchains" / version.replace("/", "--").replace(":", "---") / "bin"
    env = dict(os.environ)
    env["PATH"] = str(binary) + os.pathsep + env["PATH"]
    result = subprocess.run(lean_command(project, binary,["ExportKernel.lean"]),
                            cwd=project, env=env, capture_output=True, text=True, encoding="utf-8", timeout=120)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    instructions = [line.split() for line in result.stdout.splitlines() if line.startswith(("imm ", "load ", "store "))]
    assert len(instructions) == 64, result.stdout
    report = {"program": "SmcTuring.Dolan.Mov.kernelProgram", "instructions": instructions,
              "exporter_sha256": hashlib.sha256((project / "ExportKernel.lean").read_bytes()).hexdigest(),
              "toolchain": version}
    (ROOT / "validation/kernel.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Exported", len(instructions), "checked MOV instructions", flush=True)
    return report

if __name__ == "__main__":
    export()
