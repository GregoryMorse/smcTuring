import hashlib,json,sys,urllib.request
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from memory_budget import require_budget
require_budget()
dest=Path(__file__).resolve().parent/"policy"
refresh=json.loads((dest/"refresh.json").read_text())
records=[]
def fetch(url):
    with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"smcTuring-audit"}),timeout=45) as r:
        data=r.read(4_000_001)
    assert len(data)<4_000_000
    return data
for repo in ["mathlib-initiative/formalization.yaml","PalomarRegistry/PalomarSubmission","PalomarRegistry/PalomarPolicy"]:
    pin=refresh["pins"][repo]
    tree=json.loads(fetch("https://api.github.com/repos/"+repo+"/git/trees/"+pin+"?recursive=1"))
    paths=[x["path"] for x in tree["tree"] if x["type"]=="blob"]
    if repo.endswith("formalization.yaml"):
        selected=[p for p in paths if p.startswith("schema/") and p.endswith(".json")]
    elif repo.endswith("PalomarSubmission"):
        selected=[p for p in paths if p in ["taxonomies/arxiv-categories.json","taxonomies/msc2020-codes.json"]]
    else:
        selected=[p for p in paths if any(s in p for s in ["rubric","classification"]) and p.endswith((".md",".yaml",".json"))]
    for p in selected:
        url="https://raw.githubusercontent.com/"+repo+"/"+pin+"/"+p
        data=fetch(url);target=dest/repo.split("/")[1]/p
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        records.append({"url":url,"path":str(target.relative_to(dest)),"sha256":hashlib.sha256(data).hexdigest()})
(dest/"assets.json").write_text(json.dumps(records,indent=2)+"\n",encoding="utf-8")
print(json.dumps([r["path"] for r in records],indent=2))
