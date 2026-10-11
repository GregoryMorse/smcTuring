"""Restore collector-omitted workflow bytes from the verified checkpoint package."""
import base64, hashlib, json
from pathlib import Path
from memory_budget import ROOT, require_budget
require_budget()
latest = json.loads((ROOT / "validation/remote/157.181.172.78/20261006/codex-checkpoints/latest-local.json").read_text())
project = Path(latest["project"])
assert json.loads((project.parent / "PULL_VERIFIED.json").read_text())["passed"]
manifest = json.loads((project.parent / "manifest.json").read_text())
package_path = "validation/ci-results/portable-source-package.json"
assert hashlib.sha256((project / package_path).read_bytes()).hexdigest() == manifest["checkpoint"]["sources"][package_path]
package = json.loads((project / package_path).read_text())
for name, item in package["supplementary_files"].items():
    assert name in {".github/workflows/proof-native.yml", ".github/workflows/palomar-full.yml"}, name
    data = base64.b64decode(item["base64"], validate=True)
    assert hashlib.sha256(data).hexdigest() == item["sha256"] == package["sources"][name]
    path = project / name
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for name, expected in package["sources"].items():
    assert hashlib.sha256((project / name).read_bytes()).hexdigest() == expected, name
(project.parent / "SUPPLEMENT_VERIFIED.json").write_text(json.dumps({"commit":latest["commit"], "package_sha256":manifest["checkpoint"]["sources"][package_path],"supplementary_hashes":{n:i["sha256"] for n,i in package["supplementary_files"].items()},"verified_package_files":len(package["sources"]),"passed":True},indent=2)+"\n",encoding="utf-8")
print("Restored exact workflow; verified", len(package["sources"]), "frozen package inputs")
