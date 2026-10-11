"""Download the requested auditor; inspect archive paths before extracting."""
import hashlib, json, stat, urllib.request, zipfile
from pathlib import Path
from memory_budget import ROOT, require_budget

require_budget()
url = "https://grm.web.elte.hu/supervision/palomar-submission-auditor.zip"
dest = ROOT / "validation/palomar"
dest.mkdir(parents=True, exist_ok=True)
archive = dest / "palomar-submission-auditor.zip"
with urllib.request.urlopen(url, timeout=90) as response, archive.open("wb") as out:
    while chunk := response.read(1 << 20):
        out.write(chunk)
        assert out.tell() < 50_000_000, "Unexpected auditor download size"
entries = []
with zipfile.ZipFile(archive) as z:
    assert sum(i.file_size for i in z.infolist()) < 100_000_000
    for i in z.infolist():
        assert not stat.S_ISLNK(i.external_attr >> 16), "Archive symlink"
        target = (dest / "auditor" / i.filename).resolve()
        assert target.is_relative_to((dest / "auditor").resolve()), "Unsafe archive path"
        entries.append({"name": i.filename, "bytes": i.file_size})
    z.extractall(dest / "auditor")
record = {"url": url, "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(), "entries": entries}
(dest / "download.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
print(json.dumps(record, indent=2))
