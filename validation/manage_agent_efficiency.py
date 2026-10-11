"""Task-scoped efficiency changes over SSH; local use requires the memory guard."""
import argparse, json, subprocess, sys
from pathlib import Path
from memory_budget import ROOT, require_budget
require_budget()
sys.stdout.reconfigure(encoding='utf-8')
parser=argparse.ArgumentParser()
parser.add_argument('action',choices=['model-menu','keys','message','stage','inspect','validate-settings','verify-staged','persist-launcher','persist-config'])
parser.add_argument('value',nargs='?')
args=parser.parse_args()
payload={'action':args.action,'value':args.value}
if args.action=='message':payload['value']=(ROOT/args.value).read_text(encoding='utf-8')
if args.action=='stage':
 manifest=json.loads((ROOT/args.value).read_text(encoding='utf-8'))
 payload['files']=[{'target':item['target'],'content':(ROOT/item['source']).read_text(encoding='utf-8')} for item in manifest]
remote=r'''
import hashlib,json,subprocess,time
from pathlib import Path
from datetime import datetime,timezone
payload=json.loads(PAYLOAD)
task=Path('/home/morse/smcTuring-proof-20261006')
def run(args,**kw):return subprocess.run(args,check=True,capture_output=True,text=True,**kw).stdout
panes=run(['tmux','list-panes','-t','smc','-F','#{pane_id}|#{pane_current_command}|#{pane_current_path}']).strip().splitlines()
assert len(panes)==1
target,command,cwd=panes[0].split('|',2)
assert command=='codex' and cwd==str(task/'project')
scope=run(['systemctl','--user','show','smcturing-codex-20261006.scope','-p','ActiveState','-p','MemoryMax','-p','MemorySwapMax'])
assert 'ActiveState=active' in scope and 'MemoryMax=7500000000' in scope and 'MemorySwapMax=0' in scope
screen=lambda:run(['tmux','capture-pane','-p','-t',target,'-S','-28'])
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
result={'action':payload['action'],'stamp':stamp,'scope_unchanged':True}
if payload['action']=='persist-config':
 import shutil
 assert not (task/'agent/checkpoint-candidate.json').exists(),'Preserve an armed checkpoint'
 source=task/'agent/efficiency/efficiency.config.toml';path=task/'project/.codex/config.toml'
 manifest=json.loads((task/'agent/efficiency/install-manifest.json').read_text())
 expected=next(item['sha256'] for item in manifest if item['target']=='project/.codex/config.toml')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
 assert not path.exists() or path.read_bytes()==source.read_bytes(),'Preserve other task settings'
 path.parent.mkdir(exist_ok=True)
 temp=path.with_name('config.toml.efficiency.tmp');shutil.copyfile(source,temp);temp.replace(path)
 result['configuration']={'path':str(path),'sha256':expected,'content':path.read_text(),'task_only':True,'no_restart':True}
 receipt=task/'project/validation/remote-evidence/efficiency-adoption.json'
 record=json.loads(receipt.read_text());assert record['passed']
 record['configuration_installation_complete']=True
 record['coordinator_configuration']=result['configuration']
 record['configuration_completed_at']=stamp
 record['protected_pending_target']=None
 temp=receipt.with_suffix('.tmp');temp.write_text(json.dumps(record,indent=2)+'\n');temp.replace(receipt)
 result['adoption']=record
 features=run(['/home/morse/.local/bin/codex','-C',str(task/'project'),'features','list'])
 result['effective_features']=[line for line in features.splitlines() if line.split() and line.split()[0] in ['fast_mode','memories']]
if payload['action']=='verify-staged':
 import ast,os
 staged=task/'agent/efficiency';records=[]
 for path in staged.glob('*.py'):
  ast.parse(path.read_text(),filename=str(path));records.append(path.name)
 env=dict(os.environ,TMPDIR=str(task/'tmp'))
 test=subprocess.run(['python3',str(staged/'test_remote_reuse.py')],env=env,capture_output=True,text=True)
 result['tests']={'exit':test.returncode,'stdout':test.stdout,'stderr':test.stderr}
 result['syntax_checked']=records
 run(['bash','-n',str(staged/'launch.sh')])
 assert test.returncode==0,result['tests']
if payload['action']=='persist-launcher':
 import shutil,os
 source=task/'agent/efficiency/launch.sh';path=task/'agent/launch.sh'
 assert path.is_file() and source.is_file()
 original=path.read_text();replacement=source.read_text()
 for text in [original,replacement]:
  assert 'MemoryMax=7500000000' in text and 'MemorySwapMax=0' in text and 'CPUQuota=800%' in text
  assert '--no-daemon' in text and '--sandbox workspace-write' in text
  assert str(task) in text and 'turn_checkpoint.py' in text
 run(['bash','-n',str(source)])
 backup=path.with_name('launch.sh.before-efficiency-'+stamp);shutil.copyfile(path,backup)
 mode=path.stat().st_mode;temp=path.with_name('launch.sh.efficiency.tmp')
 shutil.copyfile(source,temp);os.chmod(temp,mode);temp.replace(path)
 result['launcher']={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'backup':str(backup),'no_restart':True}
if payload['action']=='validate-settings':
 flags=['-c','model_reasoning_effort="medium"','-c','service_tier="default"',
  '--disable','fast_mode','--disable','memories','-c','memories.generate_memories=false','-c','memories.use_memories=false']
 validation=subprocess.run(['/home/morse/.local/bin/codex',*flags,'features','list'],capture_output=True,text=True)
 result['validation']={'exit':validation.returncode,'flags':flags,
  'selected_features':[line for line in validation.stdout.splitlines() if line.split() and line.split()[0] in ['fast_mode','memories']],
  'stderr':validation.stderr}
 config=task/'project/.codex/config.toml'
 result['project_config_exists']=config.exists()
 if config.exists():result['project_config']=config.read_text()
if payload['action'] in ['model-menu','message']:
 assert any(line.strip()=='\u203a Ask Codex to do anything' for line in screen().splitlines()[-24:]),'Preserve nonempty user input'
 text='/model' if payload['action']=='model-menu' else payload['value']
 buffer='smc-efficiency-'+stamp
 run(['tmux','load-buffer','-b',buffer,'-'],input=text)
 run(['tmux','paste-buffer','-p','-b',buffer,'-t',target])
 run(['tmux','send-keys','-t',target,'Enter'])
 run(['tmux','delete-buffer','-b',buffer])
 if payload['action']=='message':
  path=task/'agent/coordinator-messages'/(stamp+'-efficiency.txt');path.parent.mkdir(exist_ok=True)
  path.write_text(text+'\n');result['remote_note']=str(path)
  result['sha256']=hashlib.sha256(text.encode()).hexdigest()
elif payload['action']=='keys':
 keys=payload['value'].split(',')
 assert all(k in ['Up','Down','Enter','Escape','Tab','s'] for k in keys)
 run(['tmux','send-keys','-t',target,*keys])
elif payload['action']=='stage':
 records=[]
 for item in payload['files']:
  path=(task/item['target']).resolve()
  assert path.is_relative_to(task) and path!=task
  # Stage outside the project so a running audit's frozen inputs are untouched.
  assert path.is_relative_to(task/'agent/efficiency')
  path.parent.mkdir(parents=True,exist_ok=True)
  if path.exists():path.with_name(path.name+'.before-'+stamp).write_bytes(path.read_bytes())
  path.write_text(item['content'],encoding='utf-8')
  records.append({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
 result['files']=records
time.sleep(.3)
result['screen']=screen()
print(json.dumps(result))
'''.replace('PAYLOAD',repr(json.dumps(payload)))
proc=subprocess.run(['ssh','-o','BatchMode=yes','-o','StrictHostKeyChecking=yes','-o','ConnectTimeout=10','157.181.172.78','python3 -'],input=remote,capture_output=True,text=True,encoding='utf-8',timeout=50)
assert proc.returncode==0,proc.stderr
result=json.loads(proc.stdout)
out=ROOT/'validation/.build'/('agent-efficiency-'+args.action+'-'+result['stamp']+'.json')
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))
