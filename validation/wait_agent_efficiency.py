"""Wait for the completed adoption receipt; collect operational evidence, never live proof edits."""
import json,subprocess,sys
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
sys.stdout.reconfigure(encoding='utf-8')
remote=r'''
import hashlib,json,time
from pathlib import Path
task=Path('/home/morse/smcTuring-proof-20261006');root=task/'project'
receipt=root/'validation/remote-evidence/efficiency-adoption.json'
deadline=time.monotonic()+480
while not receipt.exists():
 if time.monotonic()>deadline:raise TimeoutError('No completed adoption receipt yet; current build was not interrupted')
 time.sleep(2)
record=json.loads(receipt.read_text());assert record['passed']
report_path=root/'validation/remote-evidence/lean.json'
report=json.loads(report_path.read_text())
assert hashlib.sha256(report_path.read_bytes()).hexdigest()==record['report_sha256'],'Proof report has advanced; use the immutable next checkpoint'
log=Path(record.get('log',str(task/'build-efficiency-adoption.log')))
backups=sorted((task/'agent/efficiency/backups').iterdir())
backup=Path(record.get('backup',str(backups[-1])))
files={'efficiency-adoption.json':receipt.read_text(),'adoption-lean.json':report_path.read_text(),
 'adoption-resource.json':(root/'validation/remote-evidence/resource.json').read_text(),
 'adoption-toolchain.json':(root/'validation/remote-evidence/toolchain.json').read_text(),
 'adoption-axiom-audit.log':(root/'validation/remote-evidence/axiom-audit.log').read_text(),
 'adoption-build.log':log.read_text(),'task-config.toml':(root/'.codex/config.toml').read_text(),
 'prior-lean.json':(backup/'lean.json').read_text(),
 'prior-resource.json':(backup/'resource.json').read_text(),
 'launcher-before.sh':(task/'agent/launch.sh.before-efficiency-20261009T115613Z').read_text()}
print(json.dumps({'receipt':record,'files':files}))
'''
proc=subprocess.run(['ssh','-o','BatchMode=yes','-o','StrictHostKeyChecking=yes','-o','ConnectTimeout=10','157.181.172.78','python3 -'],input=remote,capture_output=True,text=True,encoding='utf-8',timeout=510)
assert proc.returncode==0,proc.stderr
record=json.loads(proc.stdout)
stamp=record['receipt'].get('installed_at',record['receipt'].get('configuration_completed_at','adopted-20261009'))
folder=ROOT/'validation/remote/157.181.172.78/20261006/efficiency'/stamp
folder.mkdir(parents=True,exist_ok=True)
for name,content in record['files'].items():
 assert Path(name).name==name
 (folder/name).write_bytes(content.encode('utf-8'))
print('Completed adoption evidence collected:',folder)
print(json.dumps(record['receipt']))
