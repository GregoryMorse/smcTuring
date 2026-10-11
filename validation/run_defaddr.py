"""Assemble and execute the literal and corrected DEFADDR on x86 and x64."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from memory_budget import require_budget

ROOT = Path(__file__).resolve().parents[1]


def vc_environment(architecture: str) -> dict[str, str]:
    require_budget()
    probe = Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"))
    probe /= "Microsoft Visual Studio/Installer/vswhere.exe"
    result = subprocess.run([str(probe), "-latest", "-products", "*",
                             "-requires", "Microsoft.VisualStudio.Component.VC.Tools.x86.x64",
                             "-property", "installationPath"],
                            check=True, capture_output=True, text=True)
    batch = Path(result.stdout.strip()) / "VC/Auxiliary/Build/vcvarsall.bat"
    result = subprocess.run('call "' + str(batch) + '" ' + architecture + ' >nul && set',
                            shell=True, executable=os.environ.get("COMSPEC", r"C:\Windows\System32\cmd.exe"), capture_output=True,
                            text=True, errors="replace")
    if result.returncode:
        raise RuntimeError("Visual Studio environment setup failed: " + result.stderr)
    # Windows variable names are case-insensitive, including cmd's Path.
    environment = {key.upper(): value for key, value in os.environ.items()}
    for line in result.stdout.splitlines():
        if "=" in line and not line.startswith("="):
            key, value = line.split("=", 1)
            environment[key.upper()] = value
    return environment


def run(command: list[str], folder: Path, environment: dict[str, str]) -> str:
    require_budget()
    result = subprocess.run(command, cwd=folder, env=environment,
                            capture_output=True, text=True, errors="replace", timeout=120)
    output = result.stdout + result.stderr
    if result.returncode:
        raise RuntimeError(str(command) + "\n" + output)
    return output


def main() -> None:
    report = {"as_of": "2026-10-03", "purpose": "DEFADDR differential native test",
              "sources": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                          for name in ["smcTuring/pure_smc.inc", "validation/defaddr_native.asm",
                                       "validation/defaddr_native.cpp"]}, "runs": []}
    for architecture in ["x86", "x64"]:
        folder = ROOT / "validation/.build/defaddr" / architecture
        folder.mkdir(parents=True, exist_ok=True)
        environment = vc_environment(architecture)
        def tool(name: str) -> str:
            found = shutil.which(name, path=environment["PATH"])
            if not found:
                raise RuntimeError("Missing " + name)
            return found
        assembly = [tool("ml64.exe" if architecture == "x64" else "ml.exe"),
                    "/nologo", "/c", "/Fo" + str(folder / "native.obj"),
                    "/Fl" + str(folder / "native.lst"), "/I" + str(ROOT / "smcTuring")]
        if architecture == "x64":
            assembly += ["/DX64"]
        else:
            assembly += ["/safeseh"]
        assembly += [str(ROOT / "validation/defaddr_native.asm")]
        build = run(assembly, folder, environment)
        build += run([tool("cl.exe"), "/nologo", "/std:c++17", "/O2", "/EHsc", "/W4",
                      "/c", str(ROOT / "validation/defaddr_native.cpp"),
                      "/Fo" + str(folder / "harness.obj")], folder, environment)
        executable = folder / "defaddr.exe"
        build += run([tool("link.exe"), "/nologo", "/SECTION:.text,ERW",
                      "/OUT:" + str(executable), str(folder / "harness.obj"),
                      str(folder / "native.obj")], folder, environment)
        (folder / "build.log").write_text(build, encoding="utf-8")
        output = run([str(executable)], folder, environment)
        disassembly = run([tool("dumpbin.exe"), "/DISASM", str(folder / "native.obj")],
                          folder, environment)
        (folder / "native.disasm.txt").write_text(disassembly, encoding="utf-8")
        (folder / "run.log").write_text(output, encoding="utf-8")
        expected = "DEFADDR " + ("64" if architecture == "x64" else "32") + "-bit: PASS 20324 cases"
        assert expected in output, output
        report["runs"].append({"architecture": architecture, "passed": True,
                               "cases": 20324, "output": output,
                               "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                               "disassembly_sha256": hashlib.sha256(disassembly.encode()).hexdigest(),
                               "build_commands": [assembly]})
        print(output.strip(), flush=True)
        (ROOT / "validation/defaddr.json").write_text(json.dumps(report, indent=2) + "\n",
                                                       encoding="utf-8")


if __name__ == "__main__":
    main()
