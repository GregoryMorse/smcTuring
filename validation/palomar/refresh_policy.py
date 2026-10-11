"""Retain exact official policy/tool/schema inputs for this submission audit."""
import hashlib, json, sys, urllib.request
from datetime import datetime, timezone
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from memory_budget import require_budget
require_budget()
out = Path(__file__).resolve().parent / "policy"
out.mkdir(exist_ok=True)
records = []
def fetch(url, name):
    req = urllib.request.Request(url, headers={"User-Agent":"smcTuring-submission-audit"})
    try:
        with urllib.request.urlopen(req, timeout=45) as r:
            data = r.read(4_000_001)
            assert len(data) <= 4_000_000
        (out / name).parent.mkdir(parents=True, exist_ok=True)
        (out / name).write_bytes(data)
        records.append({"url":url,"file":name,"sha256":hashlib.sha256(data).hexdigest(),"bytes":len(data),"passed":True})
        return data
    except Exception as e:
        records.append({"url":url,"file":name,"passed":False,"error":str(e)})
        return None
pins = {}
targets = {
 "PalomarRegistry/PalomarPolicy":["CONTRIBUTING.md","docs/specification.md"],
 "PalomarRegistry/PalomarSubmission":["toolchains.json",".github/workflows/submission.yml"],
 "PalomarRegistry/PalomarTemplate":["formalization.yaml","comparator.json","Challenge.lean","Solution.lean","lakefile.toml"],
 "mathlib-initiative/formalization.yaml":["README.md","schema/v0.4.schema.json"],
}
for repo, files in targets.items():
    data = fetch("https://api.github.com/repos/"+repo+"/commits/main", repo.replace("/","-")+"-commit.json")
    if data is None: continue
    pin = json.loads(data)["sha"]
    assert len(pin)==40 and all(c in "0123456789abcdef" for c in pin)
    pins[repo] = pin
    for file in files:
        fetch("https://raw.githubusercontent.com/"+repo+"/"+pin+"/"+file,repo.split("/")[1]+"/"+file)
fetch("https://submit.palomar-registry.org/llms.txt","llms.txt")
fetch("https://submit.palomar-registry.org/","form.html")
fetch("https://palomar-registry.org/how-to-submit","how-to-submit.html")
(out / "refresh.json").write_text(json.dumps({"refreshed_at":datetime.now(timezone.utc).isoformat(),"pins":pins,"sources":records},indent=2)+"\n",encoding="utf-8")
print(json.dumps({"pins":pins,"failed":[r for r in records if not r["passed"]],"files":len(records)},indent=2))
