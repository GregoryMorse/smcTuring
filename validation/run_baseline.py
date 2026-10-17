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


def find_msbuild(version: str | None = None) -> Path:
    probe = Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"))
    probe /= "Microsoft Visual Studio/Installer/vswhere.exe"
    command = [str(probe), "-latest", "-products", "*", "-requires",
               "Microsoft.Component.MSBuild", "-property", "installationPath"]
    if version:
        command += ["-version", {"2022": "[17.0,18.0)", "2026": "[18.0,19.0)"}[version]]
    result = subprocess.run(
        command,
        check=True, capture_output=True, text=True)
    if not result.stdout.strip():
        raise RuntimeError("Requested Visual Studio installation was not found: " + str(version))
    return Path(result.stdout.strip()) / "MSBuild/Current/Bin/MSBuild.exe"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", default="baseline.json")
    parser.add_argument("--as-of", required=True)
    parser.add_argument("--vs-version", choices=["2022", "2026"])
    parser.add_argument("--solution-output", action="store_true",
                        help="Build the convenience solution using its default isolated output paths")
    args = parser.parse_args()
    if args.solution_output and not args.vs_version:
        parser.error("--solution-output requires --vs-version")
    report = {"as_of": args.as_of, "purpose": "comparison simulator regression baseline",
              "sources": {name: digest(ROOT / name) for name in
                          ["smcTuring/main.cpp", "smcTuring/tm.asm", "smcTuring.sln",
                           "smcTuring/smcTuring.vcxproj", "smcTuring/smcTuring.vcxproj.filters"]}, "runs": []}
    report_path = ROOT / "validation" / args.report
    msbuild = find_msbuild(args.vs_version)
    report["visual_studio"] = args.vs_version or "latest installed"
    report["solution_default_outputs"] = args.solution_output
    for configuration, platform in CONFIGURATIONS:
        label = configuration + "-" + platform
        toolset = {"2022": "v143", "2026": "v145"}.get(args.vs_version)
        folder = (ROOT / "build/msbuild" / toolset / platform / configuration
                  if args.solution_output else ROOT / "validation/.build/baseline" / label)
        folder.mkdir(parents=True, exist_ok=True)
        target = "smcTuring.sln" if args.solution_output else "smcTuring/smcTuring.vcxproj"
        solution_platform = "x86" if args.solution_output and platform == "Win32" else platform
        command = [str(msbuild), str(ROOT / target),
                   "/t:Rebuild", "/nologo", "/v:minimal",
                   "/m:1", "/nodeReuse:false",
                   "/p:Configuration=" + configuration,
                   "/p:Platform=" + solution_platform]
        if not args.solution_output:
            command += ["/p:OutDir=" + str(folder) + os.sep,
                        "/p:IntDir=" + str(folder / "obj") + os.sep]
        # A runner may use its installed MSVC toolset without retargeting the
        # original project or changing any C++/MASM source.
        toolset_override = os.environ.get('SMCTURING_MSBUILD_TOOLSET')
        if toolset_override and not args.solution_output:
            assert toolset_override in {'v143', 'v145'}, 'Unexpected MSVC toolset'
            command.append('/p:PlatformToolset=' + toolset_override)
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
            if args.solution_output:
                objects = ROOT / "build/msbuild/obj" / toolset / platform / configuration
                assert (objects / "main.obj").is_file() and (objects / "tm.obj").is_file()
                forbidden = [prefix + name for prefix in ["", "smcTuring/"]
                             for name in ["Debug", "Release", "x64", "x86", "Win32", "obj", "tmp"]]
                assert not any((ROOT / name).exists() for name in forbidden), "VS build polluted a source directory"
        print(label + (": PASS" if entry["passed"] else ": FAIL"), flush=True)
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not all(run["passed"] for run in report["runs"]):
        raise SystemExit("Baseline failed; inspect " + str(report_path))
    print("All four configurations passed: " + str(report_path), flush=True)


if __name__ == "__main__":
    main()
