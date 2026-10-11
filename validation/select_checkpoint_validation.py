"""Select changed modules whose dependency closures avoid recorded memory failures."""
import argparse
import json
import re
from pathlib import Path
from memory_budget import ROOT, require_budget

require_budget()
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-only',action='store_true',help='Defer all optional Windows Lean checks; retain actual memory-block records')
args=parser.parse_args()
path = ROOT / "validation/.build/checkpoint-integration-plan.json"
plan = json.loads(path.read_text(encoding="utf-8"))
previous = plan["previous_integration"].get("local_validation", {})
full = previous.get("full_windows_build", {})
blocks = set(full.get("known_memory_blocked_modules", []))
blocks.update(n for n in [full.get("failed_module"), full.get("current_changed_module_block")] if n)
closures = {}

def closure(name):
    if name in closures:
        return closures[name]
    source = ROOT / "lean" / (name.replace(".", "/") + ".lean")
    result = {name}
    for line in re.findall(r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)", source.read_text(encoding="utf-8"), re.M):
        for dependency in line.split("--", 1)[0].split():
            if dependency.startswith("SmcTuring."):
                result.update(closure(dependency))
    closures[name] = result
    return result

modules = [item["path"][5:-5].replace("/", ".") for item in plan["changes"]
           if item["path"].startswith("lean/SmcTuring/") and item["path"].endswith(".lean")]
skipped = {name: sorted(closure(name) & blocks) for name in modules if closure(name) & blocks}
targets = [name for name in modules if name not in skipped]
if args.source_only:
    plan['windows_memory_blocked_targets']=skipped
    plan['optional_windows_available_targets']=targets
    plan['optional_windows_checks_deferred']=True
    skipped={name:sorted(closure(name) & blocks) for name in modules}
    targets=[]
else:
    plan['optional_windows_checks_deferred']=False
plan["validation_targets"] = targets
plan["validation_scope"] = "changed_modules" if targets else "source_integrity_and_errata_only"
plan["validation_build_report"] = "validation/.build/checkpoint-partial-build.json"
plan["known_memory_blocked_modules"] = sorted(blocks)
plan["skipped_windows_targets"] = skipped
plan["local_memory_block"] = full.get("current_changed_module_block")
plan["memory_block_retried_this_integration"] = False
path.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
if args.source_only:
    print(f"Source/errata integrity selected; all {len(modules)} optional Windows Lean checks deferred. Actual prior memory-block dependencies retained separately.")
else:
    print(f"Selected {len(targets)} of {len(modules)} changed modules; {len(skipped)} depend on previously memory-blocked modules.")
for name in targets:
    print(name)
