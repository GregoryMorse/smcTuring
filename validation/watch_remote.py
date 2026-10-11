"""Fetch remote sources, checkpoints and new proof artifacts until the unit stops."""
import io,json,subprocess,sys,tarfile,time
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
sys.stdout.reconfigure(encoding="utf-8")
HOST="157.181.172.78"
TASK="/home/morse/smcTuring-proof-20261006"
DEST=ROOT/"validation/remote"/HOST/"20261006"
DEST.mkdir(parents=True,exist_ok=True)
SSH=["ssh","-o","BatchMode=yes","-o","StrictHostKeyChecking=yes",HOST]
SCP=["scp","-o","BatchMode=yes","-o","StrictHostKeyChecking=yes"]
def remote(code,scope=False):
 command="python3 -" if not scope else "systemd-run --user --scope --quiet -p MemoryMax=250000000 -p MemorySwapMax=0 -p CPUQuota=100% python3 -"
 result=subprocess.run(SSH+[command],input=code,capture_output=True,text=True,encoding="utf-8",timeout=180)
 assert result.returncode==0,result.stdout+result.stderr
 return json.loads(result.stdout)
last=-1
for attempt in range(120):
 status=remote("""import json,subprocess
from pathlib import Path
root=Path('/home/morse/smcTuring-proof-20261006')
evidence=root/'project/validation/remote-evidence'
p=evidence/'build-progress.json'
progress=json.loads(p.read_text()) if p.exists() else {}
state=subprocess.run(['systemctl','--user','show','smcturing-20261006-proof.service','-p','ActiveState','--value'],capture_output=True,text=True).stdout.strip()
print(json.dumps(dict(state=state,compiled=progress.get('compiled',0),passed=(evidence/'lean.json').exists())))
""")
 count=status['compiled'];finished=status['state'] not in ['active','activating','reloading']
 if last<0 or count>=last+10 or finished:
  code="""import json,tarfile
from pathlib import Path
root=Path('/home/morse/smcTuring-proof-20261006');project=root/'project'
evidence=project/'validation/remote-evidence'
progress=json.loads((evidence/'build-progress.json').read_text()) if (evidence/'build-progress.json').exists() else {}
old=OLD_COUNT
archive=root/'checkpoint-fetch.tar'
paths=list(evidence.glob('*'))+[root/'build-78.log',root/'launch-78.json',root/'transfer-verified.json']
paths+=list((project/'lean').glob('*.lean'))+list((project/'lean/SmcTuring').rglob('*.lean'))
paths+=[project/'validation/remote_build.py',project/'validation/remote_artifacts.py',project/'AGENTS.md']
for index,record in enumerate(progress.get('modules',{}).values()):
 if index>=old:
  paths+=[project/path for path in record['artifacts']]
with tarfile.open(archive,'w') as output:
 for path in paths:
  if path.is_file():output.add(path,arcname=str(path.relative_to(root)),recursive=False)
print(json.dumps(dict(archive=str(archive),bytes=archive.stat().st_size,compiled=progress.get('compiled',0))))
""".replace('OLD_COUNT',str(max(last,0) if count>=last else 0))
  bundle=remote(code,scope=True)
  archive=DEST/'checkpoint-fetch.tar'
  subprocess.run(SCP+[HOST+':'+bundle['archive'],str(archive)],check=True,timeout=300)
  with tarfile.open(archive) as source:
   for member in source.getmembers():
    assert member.isfile() and not Path(member.name).is_absolute() and '..' not in Path(member.name).parts,member.name
   source.extractall(DEST/'checkpoint')
  last=bundle['compiled']
  print('Fetched checkpoint: '+str(last)+' compiled modules; '+str(bundle['bytes'])+' bytes; '+status['state'],flush=True)
  (DEST/'watch-status.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
 if finished:
  if not status['passed']:raise SystemExit('Remote job stopped without a passing complete audit; checkpoint fetched.')
  print('Remote complete axiom audit fetched.',flush=True);break
 time.sleep(15)
else:raise SystemExit('Watch limit reached; last checkpoint preserved.')
