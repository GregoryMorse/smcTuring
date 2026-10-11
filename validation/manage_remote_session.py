"""Task-scoped Codex session maintenance; local execution requires the guard."""
import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from memory_budget import ROOT, require_budget

require_budget()
sys.stdout.reconfigure(encoding="utf-8")
parser = argparse.ArgumentParser()
parser.add_argument("action", choices=["inspect", "stop", "start", "trust", "status", "resume"])
args = parser.parse_args()
remote = r'''
import hashlib,json,subprocess,time,shlex
from pathlib import Path
task=Path('/home/morse/smcTuring-proof-20261006')
binary=Path('/home/morse/.local/bin/codex')
thread='01a11131-6044-72f2-ad61-43089313f1b5'
action=ACTION
def run(argv):
 p=subprocess.run(argv,capture_output=True,text=True,timeout=20)
 return {'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
pane=run(['tmux','list-panes','-t','smc','-F','#{pane_id}|#{pane_pid}|#{pane_current_command}|#{pane_current_path}|#{pane_dead}'])
scope=run(['systemctl','--user','show','smcturing-codex-20261006.scope','-p','ActiveState','-p','ControlGroup','-p','MemoryMax','-p','MemorySwapMax','-p','CPUQuotaPerSecUSec','-p','TasksCurrent','-p','TasksMax'])
def processes():
 state=run(['systemctl','--user','show','smcturing-codex-20261006.scope','-p','ControlGroup'])['stdout'].strip()
 group=state.split('=',1)[1] if '=' in state else ''
 if not group:return []
 cg=Path('/sys/fs/cgroup')/group.lstrip('/')
 result=[]
 for file in cg.rglob('cgroup.procs'):
  for pid in file.read_text().splitlines():
   try:
    exe=Path('/proc')/pid/'exe';name=exe.resolve().name
    argv=(Path('/proc')/pid/'cmdline').read_bytes().replace(b'\0',b' ').decode()
    item={'pid':int(pid),'executable':str(exe.resolve())}
    if name=='codex':
     item.update(cmdline=argv,running_version=run([str(exe),'--version']))
    item['proof_job']=name in ['lean','lake','clang','gcc','g++'] or any(s in argv for s in ['remote_build.py','check_target.py','bounded_build.py'])
    result.append(item)
   except (FileNotFoundError,ProcessLookupError):pass
 return result
records=processes()
sessions=list((Path.home()/'.codex/sessions').rglob('*'+thread+'*.jsonl'))
assert len(sessions)==1, 'Expected the existing task thread'
with sessions[0].open() as f:meta=json.loads(f.readline())
assert meta['payload']['id']==thread
tail=run(['tmux','capture-pane','-p','-t','smc','-S','-20'])
disk=run([str(binary),'--version'])
assert disk['exit']==0 and disk['stdout'].strip()=='codex-cli 0.162.1',disk
upgrade=task/'agent/session-upgrade';upgrade.mkdir(exist_ok=True)
operation={}
if action=='trust':
 assert 'Trust this folder?' in tail['stdout'] and str(task/'project') in tail['stdout']
 assert '\u203a 1. Trust and continue' in tail['stdout'],'Trust only the explicitly authorized task folder'
 target=pane['stdout'].strip().split('|')[0]
 assert run(['tmux','send-keys','-t',target,'Enter'])['exit']==0
 time.sleep(.5)
 operation={'authorized_task_folder_trusted':str(task/'project')}
if action=='stop':
 assert 'Goal paused (/goal resume)' in '\n'.join(tail['stdout'].strip().splitlines()[-10:]),'Goal must be paused'
 input_lines='\n'.join(tail['stdout'].strip().splitlines()[-10:])
 assert '\u203a Ask Codex to do anything' in input_lines or '\u203a /quit' in input_lines,'Preserve user input'
 assert not (task/'agent/checkpoint-candidate.json').exists(),'Do not interrupt an armed checkpoint'
 assert not any(p['proof_job'] for p in records),'Do not interrupt a proof job'
 (upgrade/'before-pane.txt').write_text(tail['stdout'])
 run(['tmux','set-option','-w','-t','smc','remain-on-exit','on'])
 target=pane['stdout'].strip().split('|')[0]
 if '\u203a /quit' not in input_lines:
  assert run(['tmux','send-keys','-t',target,'-l','/quit'])['exit']==0
  time.sleep(.5)
 assert run(['tmux','send-keys','-t',target,'Enter'])['exit']==0
 for _ in range(16):
  current=processes()
  if not current:break
  time.sleep(.25)
 if processes():
  # The verified paused task has no active proof jobs; stop only its own scope.
  assert not any(p['proof_job'] for p in processes())
  assert run(['systemctl','--user','stop','smcturing-codex-20261006.scope'])['exit']==0
 assert not processes(),'Old task scope has not drained; do not start another agent'
 operation={'stopped':True,'thread_preserved':True,'old_processes':records}
if action=='start':
 assert not processes(),'Task scope must be empty before restart'
 assert run(['tmux','list-panes','-t','smc','-F','#{pane_current_command}'])['stdout'].strip() in ['bash','sh'], 'Expected existing shell'
 source=(task/'agent/launch.sh').read_text()
 for required in ['MemoryMax=7500000000','MemorySwapMax=0','CPUQuota=800%','TasksMax=512','--no-daemon','--sandbox workspace-write','--ask-for-approval never','model_reasoning_effort="medium"','service_tier="default"','--disable fast_mode --disable memories','turn_checkpoint.py']:
  assert required in source,required
 launcher=upgrade/'resume-0.162.1.sh'
 launcher.write_text(source.rstrip()+' \\\n resume '+shlex.quote(thread)+'\n')
 assert run(['bash','-n',str(launcher)])['exit']==0
 target=pane['stdout'].strip().split('|')[0]
 assert run(['tmux','send-keys','-t',target,'-l','bash '+shlex.quote(str(launcher))])['exit']==0
 time.sleep(.5)
 assert run(['tmux','send-keys','-t',target,'Enter'])['exit']==0
 for _ in range(40):
  if any('resume '+thread in p.get('cmdline','') for p in processes()):break
  time.sleep(.25)
 current=processes()
 matches=[p for p in current if 'resume '+thread in p.get('cmdline','')]
 assert len(matches)==1,current
 assert matches[0]['running_version']['stdout'].strip()=='codex-cli 0.162.1',matches
 operation={'started':True,'launcher':str(launcher),'launcher_sha256':hashlib.sha256(launcher.read_bytes()).hexdigest(),'running_process':matches[0]}
if action=='resume':
 matches=[p for p in records if 'resume '+thread in p.get('cmdline','')]
 assert len(matches)==1 and matches[0]['running_version']['stdout'].strip()=='codex-cli 0.162.1',records
 for required in ['MemoryMax=7500000000','MemorySwapMax=0','CPUQuotaPerSecUSec=8s','TasksMax=512','ActiveState=active']:
  assert required in scope['stdout'],required
 target=pane['stdout'].strip().split('|')[0]
 if 'Resume paused goal?' in tail['stdout']:
  assert '\u203a 1. Resume goal' in tail['stdout'] and 'Complete the full corrected Morse 2018 paper' in tail['stdout']
 else:
  assert 'Goal paused (/goal resume)' in '\n'.join(tail['stdout'].strip().splitlines()[-10:]),'Resume only the paused existing goal'
  assert '\u203a Ask Codex to do anything' in '\n'.join(tail['stdout'].strip().splitlines()[-10:]),'Preserve user input'
  assert run(['tmux','send-keys','-t',target,'-l','/goal resume'])['exit']==0
  time.sleep(.5)
 assert run(['tmux','send-keys','-t',target,'Enter'])['exit']==0
 operation={'resume_requested':True,'thread_preserved':True}
record={'action':action,'binary':str(binary),'disk_version':disk,
 'pane':pane,'scope':scope,'processes':records,'operation':operation,
 'thread':thread,'thread_file':str(sessions[0]),'session_metadata':{k:meta['payload'].get(k) for k in ['id','cwd','cli_version']},
 'pane_tail':run(['tmux','capture-pane','-p','-t','smc','-S','-20']),
 'launcher':(task/'agent/launch.sh').read_text(),
 'candidate_armed':(task/'agent/checkpoint-candidate.json').exists(),
 'published_commit':json.loads((task/'agent/latest-checkpoint.json').read_text())['commit']}
(upgrade/(action+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
'''
remote=remote.replace('ACTION',repr(args.action))
result = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes",
    "-o", "ConnectTimeout=10", "157.181.172.78", "python3 -"],
    input=remote, capture_output=True, text=True, encoding="utf-8", timeout=65)
assert result.returncode == 0, result.stderr
record = json.loads(result.stdout)
record["checked_at"] = datetime.now(timezone.utc).isoformat()
archive = ROOT/"validation/remote/157.181.172.78/20261006/session-upgrade"
archive.mkdir(exist_ok=True)
receipt = archive/(datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")+"-"+args.action+".json")
receipt.write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
summary = {k: record[k] for k in ["action", "disk_version", "operation", "thread", "published_commit"]}
summary["scope"] = record["scope"]["stdout"].strip()
summary["processes"] = record["processes"]
summary["screen"] = record["pane_tail"]["stdout"].strip()[-6000:]
print(json.dumps(summary, indent=2))
print("Receipt:", receipt)
