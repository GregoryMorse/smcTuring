"""Restore immutable CI source data, distinct from historical validation reports."""
import hashlib,json,shutil
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
latest=json.loads((ROOT/"validation/remote/157.181.172.78/20261006/codex-checkpoints/latest-local.json").read_text())
remote=Path(latest["project"])
manifest=json.loads((remote.parent/"manifest.json").read_text())
package=json.loads((remote/"validation/ci-results/portable-source-package.json").read_text())
restored={}
for name in ["validation/ci/pins.json","validation/ci/native-proof-contract.json","validation/ci/reference/morse-2018-errata.log"]:
    data=(remote/name).read_bytes()
    sha=hashlib.sha256(data).hexdigest()
    assert sha==manifest["checkpoint"]["sources"][name]==package["sources"][name]
    target=ROOT/name
    assert not target.exists() or target.read_bytes()==data, "Review local conflict: "+name
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
    restored[name]=sha
(ROOT/"validation/palomar/ci-input-restoration.json").write_text(json.dumps({"commit":latest["commit"],"restored":restored,"passed":True},indent=2)+"\n",encoding="utf-8")
print("Restored",len(restored),"source-bound CI data/reference files")
