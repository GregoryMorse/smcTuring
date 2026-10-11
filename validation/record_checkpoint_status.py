"""Preserve a coordinator activity check without creating or promoting a checkpoint."""
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path
from memory_budget import ROOT, require_budget

require_budget()
base = ROOT / "validation/remote/157.181.172.78/20261006"
integration = json.loads((base / "latest-integration.json").read_text(encoding="utf-8"))
latest = json.loads((base / "codex-checkpoints/latest-local.json").read_text(encoding="utf-8"))
live_path = ROOT / "validation/.build/checkpoint-live-progress.json"
live = json.loads(live_path.read_text(encoding="utf-8"))
assert integration["commit"] == latest["commit"] == live["published"]["commit"], "Integrate the newly published checkpoint before recording this status"
stamp = datetime.now(timezone.utc)
archive = base / "status-rechecks" / (stamp.strftime("%Y%m%dT%H%M%SZ") + "-" + latest["commit"][:7])
archive.mkdir(parents=True, exist_ok=False)
for path in [live_path, ROOT / "validation/.build/memory-checkpoint-live-progress.json", ROOT / "validation/.build/memory-checkpoint-pull.json"]:
    shutil.copyfile(path, archive / path.name)
record = {"checked_at": live["checked_at"], "checkpoint": latest["commit"],
          "state": "latest_checkpoint_already_integrated", "new_source_promotions": 0,
          "full_paper_complete": False, "live_work_is_audited_proof_evidence": False,
          "integration_report": str(base / "latest-integration.json"),
          "local_validation_state": integration["local_validation"]["state"],
          "archive": str(archive), "live_task": live["live_status"]["current_task"]}
(archive / "status.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
(base / "latest-status.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
audit = integration["remote_audit"]
text = f"""# Latest coordinator status

Checked: {live['checked_at']}.

The latest published end-of-turn checkpoint remains `{latest['commit']}` and is
already integrated. No further source promotion or unchanged rebuild was needed
for this activity check. Its complete Linux audit passes {audit['modules']} modules and
{audit['declarations']:,} declarations on pinned Lean 4.35.0-rc3. The prior partial
Windows verification and recorded memory blockers retain their stated scope.
Current local validation state: `{integration['local_validation']['state']}`.

The existing remote goal is active. Live task: {live['live_status']['current_task']}.
The inspected pane shows ongoing task work. These unpublished results have not passed a completed-checkpoint
audit and are not counted as proved progress.

See the closure dashboard for the current source-verified closing obligations.
Overall completion remains false.
See [the closure dashboard](../../../../lean/CLOSURE_STATUS.md) and
[the integration report](INTEGRATION.md). Activity and resource evidence is saved
in `{archive.relative_to(ROOT).as_posix()}`.
"""
(base / "STATUS.md").write_text(text, encoding="utf-8")
print("Latest checkpoint already integrated; current activity check preserved at " + str(archive))
