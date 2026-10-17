"""Rebuild and check the comparison simulators in all VS configurations."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


ROOT = Path(os.environ.get('SMCTURING_SOURCE_ROOT', Path(__file__).resolve().parents[1])).resolve()
EXPECTED = "0100_1001_ -> 1101_0000_"
CONFIGURATIONS = [("Debug", "Win32"), ("Release", "Win32"),
                  ("Debug", "x64"), ("Release", "x64")]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def find_msbuild() -> Path:
    probe = Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"))
    probe /= "Microsoft Visual Studio/Installer/vswhere.exe"
    result = subprocess.run(
        [str(probe), "-latest", "-products", "*", "-requires",
         "Microsoft.Component.MSBuild", "-property", "installationPath"],
        check=True, capture_output=True, text=True)
    return Path(result.stdout.strip()) / "MSBuild/Current/Bin/MSBuild.exe"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", default="baseline.json")
    parser.add_argument("--as-of", required=True)
    args = parser.parse_args()
    report = {"as_of": args.as_of, "purpose": "comparison simulator regression baseline",
              "sources": {name: digest(ROOT / name) for name in
                          ["smcTuring/main.cpp", "smcTuring/tm.asm",
                           "smcTuring/smcTuring.vcxproj"]}, "runs": []}
    report_path = ROOT / "validation" / args.report
    msbuild = find_msbuild()
    for configuration, platform in CONFIGURATIONS:
        label = configuration + "-" + platform
        folder = ROOT / "validation/.build/baseline" / label
        folder.mkdir(parents=True, exist_ok=True)
        command = [str(msbuild), str(ROOT / "smcTuring/smcTuring.vcxproj"),
                   "/t:Rebuild", "/nologo", "/v:minimal",
                   "/p:Configuration=" + configuration,
                   "/p:Platform=" + platform,
                   "/p:OutDir=" + str(folder) + os.sep,
                   "/p:IntDir=" + str(folder / "obj") + os.sep]
        # A runner may use its installed MSVC toolset without retargeting the
        # original project or changing any C++/MASM source.
        toolset = os.environ.get('SMCTURING_MSBUILD_TOOLSET')
        if toolset:
            assert toolset in {'v143', 'v145'}, 'Unexpected MSVC toolset'
            command.append('/p:PlatformToolset=' + toolset)
        print("Building " + label, flush=True)
        build = subprocess.run(command, cwd=ROOT, capture_output=True,
                               text=True, errors="replace", timeout=240)
        (folder / "build.log").write_text(build.stdout + build.stderr, encoding="utf-8")
        entry = {"configuration": label, "build_exit": build.returncode,
                 "build_command": command}
        report["runs"].append(entry)
        if build.returncode:
            entry["passed"] = False
            entry["error"] = build.stdout + build.stderr
        else:
            executable = folder / "smcTuring.exe"
            run = subprocess.run([str(executable)], input="\n", cwd=folder,
                                 capture_output=True, text=True, errors="replace",
                                 timeout=120)
            output = run.stdout + run.stderr
            (folder / "run.log").write_text(output, encoding="utf-8")
            lines = [line for line in run.stdout.splitlines() if " -> " in line]
            count = 9 if platform == "Win32" else 6
            entry.update(run_exit=run.returncode, output=output,
                         executable_sha256=digest(executable),
                         simulator_count=len(lines), expected_count=count,
                         passed=(run.returncode == 0 and len(lines) == count
                                 and all(line.endswith(EXPECTED) for line in lines)))
        print(label + (": PASS" if entry["passed"] else ": FAIL"), flush=True)
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not all(run["passed"] for run in report["runs"]):
        raise SystemExit("Baseline failed; inspect " + str(report_path))
    print("All four configurations passed: " + str(report_path), flush=True)


if __name__ == "__main__":
    main()
