"""Inspect the pinned public Mathlib dependency before adding its adapter."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REVISION = "302343bb9a029d4edab4f736703f0736896c1b64"
REPOSITORY = "https://github.com/leanprover-community/mathlib4.git"
BASE = "https://raw.githubusercontent.com/leanprover-community/mathlib4/" + REVISION + "/"
DESTINATION = ROOT / "validation/.cache/mathlib-metadata" / REVISION


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true", help="Resolve the pinned Lake dependency into the workspace")
    parser.add_argument("--cache", action="store_true", help="Fetch the TM0 import's precompiled dependency closure")
    arguments = parser.parse_args()
    DESTINATION.mkdir(parents=True, exist_ok=True)
    evidence = {"as_of": "2026-10-03", "repository": REPOSITORY, "revision": REVISION,
                "files": {}, "adapter_checked": False}
    for relative in ["lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json",
                     "Cache/IO.lean", "Cache/Main.lean"]:
        request = urllib.request.Request(BASE + relative, headers={"User-Agent": "smcTuring-validation"})
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                contents = response.read()
        except urllib.error.HTTPError as error:
            if error.code == 404 and relative in ["lakefile.lean", "lakefile.toml"]:
                continue
            raise
        target = DESTINATION / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(contents)
        evidence["files"][relative] = {
            "url": BASE + relative,
            "path": str(target.relative_to(ROOT)),
            "sha256": hashlib.sha256(contents).hexdigest(),
        }
        if relative == "lean-toolchain":
            observed = contents.decode().strip()
            expected = (ROOT / "lean/lean-toolchain").read_text().strip()
            assert observed == expected, (observed, expected)
            evidence["toolchain"] = observed
            print("Compatible Mathlib toolchain: " + observed, flush=True)
        elif relative == "lake-manifest.json":
            manifest = json.loads(contents)
            evidence["dependency_manifest"] = manifest
            print("Pinned transitive packages: " + ", ".join(item["name"] for item in manifest["packages"]), flush=True)
        else:
            for line_number, line in enumerate(contents.decode().splitlines(), start=1):
                if any(fragment in line.lower() for fragment in ["post_update", "postupdate", "cache_on_update",
                    "cache_dir", "xdg", "localappdata", "getenv", "cache get", "get!", "get root"]):
                    print(f"{relative}:{line_number}: {line}", flush=True)
    assert "lakefile.lean" in evidence["files"] or "lakefile.toml" in evidence["files"]
    project = ROOT / "lean"
    binary = project / ".elan/toolchains" / evidence["toolchain"].replace("/", "--").replace(":", "---") / "bin"
    lake = binary / "lake.exe"
    environment = dict(os.environ)
    environment["PATH"] = str(binary) + os.pathsep + environment["PATH"]
    environment["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    environment["MATHLIB_CACHE_DIR"] = str(ROOT / "validation/.cache/mathlib-artifacts")
    if arguments.update:
        assert lake.is_file(), lake
        subprocess.run([str(lake), "update", "mathlib"], cwd=project, env=environment, check=True)
    if arguments.update or arguments.cache:
        package = project / ".lake/packages/mathlib"
        observed = subprocess.run(["git", "-C", str(package), "rev-parse", "HEAD"],
                                  check=True, capture_output=True, text=True).stdout.strip()
        assert observed == REVISION, observed
        for relative, record in evidence["files"].items():
            assert hashlib.sha256((package / relative).read_bytes()).hexdigest() == record["sha256"], relative
        manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
        resolved = {item["name"]: item for item in manifest["packages"]}
        assert resolved["mathlib"]["rev"] == REVISION
        for dependency in evidence["dependency_manifest"]["packages"]:
            assert resolved[dependency["name"]]["rev"] == dependency["rev"], dependency["name"]
        evidence["installed_revision"] = observed
        evidence["project_manifest_sha256"] = hashlib.sha256((project / "lake-manifest.json").read_bytes()).hexdigest()
        print("Pinned dependency sources and transitive revisions match.", flush=True)
    if arguments.cache:
        subprocess.run([str(lake), "exe", "cache", "get", "Mathlib.Computability.TuringMachine.PostTuringMachine",
                        "Mathlib.Data.Fintype.Prod", "Mathlib.Data.Fintype.Option", "Mathlib.Computability.Primrec.List"],
                       cwd=project, env=environment, check=True)
        evidence["tm0_cache_ready"] = True
    (ROOT / "validation/mathlib.json").write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print("Mathlib metadata recorded; no adapter is claimed checked.", flush=True)


if __name__ == "__main__":
    main()
