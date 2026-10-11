"""Prepare an exact, task-scoped remote installation manifest without changing proof sources."""
import ast,hashlib,json,shutil
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
def digest(path):return hashlib.sha256(path.read_text(encoding='utf-8').encode('utf-8')).hexdigest()
entries=[
 ('validation/remote_build.py','remote_build.py','project/validation/remote_build.py'),
 ('validation/remote_reuse.py','remote_reuse.py','project/validation/remote_reuse.py'),
 ('validation/test_remote_reuse.py','test_remote_reuse.py','project/validation/test_remote_reuse.py'),
 ('validation/remote-agent/EFFICIENCY.md','EFFICIENCY.md','project/validation/remote-agent/EFFICIENCY.md'),
 ('validation/remote-agent/HANDOFF_CURRENT.md','HANDOFF.md','project/validation/remote-agent/HANDOFF.md'),
 ('validation/remote-agent/REMOTE_AGENTS.md','AGENTS.md','project/AGENTS.md'),
 ('validation/remote-agent/efficiency.config.toml','efficiency.config.toml','project/.codex/config.toml'),
 ('validation/remote-agent/launch.sh','launch.sh','project/validation/remote-agent/launch.sh'),
 ('validation/remote-agent/launch.sh','launch.sh','agent/launch.sh')]
install=[];stage=[];seen=set()
for source,name,target in entries:
 path=ROOT/source
 if path.suffix=='.py':ast.parse(path.read_text(encoding='utf-8'),filename=source)
 install.append({'source':name,'target':target,'sha256':digest(path)})
 if name not in seen:
  stage.append({'source':source,'target':'agent/efficiency/'+name});seen.add(name)
for name in ['adopt_efficiency.py']:
 source='validation/remote-agent/'+name;ast.parse((ROOT/source).read_text(encoding='utf-8'),filename=source)
 stage.append({'source':source,'target':'agent/efficiency/'+name})
folder=ROOT/'validation/.build';folder.mkdir(exist_ok=True)
(folder/'efficiency-install-manifest.json').write_text(json.dumps(install,indent=2)+'\n',encoding='utf-8')
stage.append({'source':'validation/.build/efficiency-install-manifest.json','target':'agent/efficiency/install-manifest.json'})
(folder/'efficiency-stage-manifest.json').write_text(json.dumps(stage,indent=2)+'\n',encoding='utf-8')
# Keep the local canonical handoff consistent; its old instructions remain archived.
old=ROOT/'validation/remote-agent/HANDOFF.md';backup=folder/'efficiency-backups/HANDOFF-20261006.md'
backup.parent.mkdir(parents=True,exist_ok=True)
if not backup.exists():shutil.copyfile(old,backup)
shutil.copyfile(ROOT/'validation/remote-agent/HANDOFF_CURRENT.md',old)
print('Prepared',len(stage),'staged files;',len(install),'exact installation targets. Python syntax passed.')
