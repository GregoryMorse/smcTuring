"""Read task activity without interrupting it or treating live files as a checkpoint."""
import json
import subprocess
import sys
from datetime import datetime, timezone
from memory_budget import ROOT, require_budget

require_budget()
sys.stdout.reconfigure(encoding="utf-8")
remote_code = r'''
import json, subprocess
from pathlib import Path
task = Path('/home/morse/smcTuring-proof-20261006')
def run(args):
    result = subprocess.run(args, capture_output=True, text=True, timeout=15)
    return {'exit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
scope = run(['systemctl', '--user', 'show', 'smcturing-codex-20261006.scope',
             '-p', 'ActiveState', '-p', 'ControlGroup', '-p', 'MemoryCurrent',
             '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'TasksCurrent', '-p', 'TasksMax'])
pane = run(['tmux', 'capture-pane', '-p', '-t', 'smc', '-S', '-60'])
panes = run(['tmux', 'list-panes', '-t', 'smc', '-F', '#{pane_pid} #{pane_current_command} #{pane_current_path}'])
status = json.loads((task/'project/REMOTE_STATUS.json').read_text())
index = json.loads((task/'agent/latest-checkpoint.json').read_text())
print(json.dumps({'scope': scope, 'panes': panes, 'pane_tail': pane,
                  'published': index,
                  'live_status': {k: status.get(k) for k in ['state', 'current_task', 'overall_complete', 'remaining']}}))
'''
command = ["ssh", "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes",
           "-o", "ConnectTimeout=10", "157.181.172.78", "python3 -"]
result = subprocess.run(command, input=remote_code, capture_output=True, text=True, encoding="utf-8", timeout=65)
assert result.returncode == 0, result.stderr
record = json.loads(result.stdout)
record["checked_at"] = datetime.now(timezone.utc).isoformat()
record["scope_of_evidence"] = "Live activity only; completed proof claims come exclusively from immutable published checkpoints"
path = ROOT/"validation/.build/checkpoint-live-progress.json"
path.write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
print("LIVE RESOURCE SCOPE\n"+record["scope"]["stdout"])
print("TASK PANE\n"+record["panes"]["stdout"])
print("LATEST PUBLISHED", record["published"].get("commit"))
print("LIVE TASK", record["live_status"])
print("LAST PANE LINES\n"+"\n".join(record["pane_tail"]["stdout"].splitlines()[-38:]))
