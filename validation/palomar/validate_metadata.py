"""Validate against the retained pinned upstream schema and registry taxonomies."""
import hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from memory_budget import ROOT,require_budget
require_budget()
import yaml,jsonschema
policy=Path(__file__).resolve().parent/"policy"
path=ROOT/"lean/formalization.yaml"
schema_path=policy/"formalization.yaml/schema/v0.4.schema.json"
data=yaml.safe_load(path.read_text(encoding="utf-8"))
schema=json.loads(schema_path.read_text(encoding="utf-8"))
jsonschema.Draft7Validator.check_schema(schema)
errors=sorted(jsonschema.Draft7Validator(schema).iter_errors(data),key=lambda e:str(e.path))
assert not errors, "\n".join(str(e) for e in errors)
classification={}
for kind,file in [("arxiv","arxiv-categories.json"),("msc2020","msc2020-codes.json")]:
    codes=json.loads((policy/"PalomarSubmission/taxonomies"/file).read_text(encoding="utf-8"))
    classification[kind]={c:codes[c] for c in data["classification"][kind]}
assert data["project"]["license"]=="CC0-1.0" and "CC0 1.0 Universal" in (ROOT/"LICENSE.txt").read_text(encoding="utf-8")
record={"passed":True,"metadata_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"schema_sha256":hashlib.sha256(schema_path.read_bytes()).hexdigest(),"schema_revision":"99c678e569c7c4c0772db297c5ddd5e4c9b6322e","pipeline_revision":"d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44","classification":classification,"license_text_match":True,"authoritative_spdx_detection_claimed":False,"scope":"Pinned upstream v0.4 schema and registry taxonomy membership, not external acceptance"}
(Path(__file__).resolve().parent/"metadata-validation.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(json.dumps(record,indent=2))
