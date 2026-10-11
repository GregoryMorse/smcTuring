"""Read task-only Codex settings and aggregate usage, without exposing conversation or credentials."""
import argparse, json, subprocess, sys
from pathlib import Path
from memory_budget import ROOT, require_budget
require_budget()
sys.stdout.reconfigure(encoding='utf-8')
parser=argparse.ArgumentParser()
parser.add_argument('--after',action='store_true',help='Save concise post-change settings/usage; preserve the baseline')
args=parser.parse_args()
remote = r'''
import json, os, subprocess
from pathlib import Path
task=Path('/home/morse/smcTuring-proof-20261006')
def run(args):
 p=subprocess.run(args,capture_output=True,text=True,timeout=20)
 return {'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
panes=run(['tmux','list-panes','-t','smc','-F','#{pane_id}|#{pane_pid}|#{pane_current_command}|#{pane_current_path}'])
pane=run(['tmux','capture-pane','-p','-t','smc','-S','-30'])
config=Path.home()/'.codex/config.toml'
allowed={'model','model_reasoning_effort','service_tier','model_auto_compact_token_limit','model_context_window','memories','features','profiles'}
try:
 import tomllib
except ImportError:
 try:
  import tomli as tomllib
 except ImportError:
  tomllib=None
if tomllib:
 parsed=tomllib.loads(config.read_text())
else:
 # Read only simple supported setting values; do not install shared packages.
 parsed={};section=[]
 for line in config.read_text().splitlines():
  line=line.strip()
  if line.startswith('[') and line.endswith(']'):
   section=line[1:-1].split('.');continue
  if '=' not in line or line.startswith('#'):continue
  key,value=map(str.strip,line.split('=',1))
  if (section[0] if section else key) not in allowed:continue
  try:value=json.loads(value)
  except ValueError:continue
  target=parsed
  for part in section:target=target.setdefault(part.strip('"'),{})
  target[key]=value
settings={k:v for k,v in parsed.items() if k in allowed}
settings['profiles']={k:{a:b for a,b in v.items() if a in allowed and a!='profiles'} for k,v in settings.get('profiles',{}).items()}
files=sorted((Path.home()/'.codex/sessions').rglob('*.jsonl'),key=lambda p:p.stat().st_mtime,reverse=True)
selected=None;meta=None
for file in files[:30]:
 with file.open() as f:
  first=json.loads(f.readline())
 if first.get('type')=='session_meta' and first.get('payload',{}).get('cwd')==str(task/'project'):
  selected=file;meta=first['payload'];break
assert selected,'Task session not found'
usage=[];contexts=[];compact=0
with selected.open() as stream:
 for line in stream:
  item=json.loads(line);payload=item.get('payload',{})
  if item.get('type')=='turn_context':
   contexts.append({k:payload.get(k) for k in ['model','effort','reasoning_effort','service_tier']})
  if item.get('type')=='compacted':compact+=1
  if item.get('type')=='event_msg' and payload.get('type')=='token_count' and payload.get('info'):
   info=payload['info'];usage.append({'timestamp':item.get('timestamp'),'last':info.get('last_token_usage'),'total':info.get('total_token_usage'),'context_window':info.get('model_context_window')})
catalog=Path.home()/'.codex/models_cache.json'
model_info=[]
if catalog.exists():
 data=json.loads(catalog.read_text())
 for model in data.get('models',[]):
  if model.get('slug')==(contexts[-1].get('model') if contexts else settings.get('model')):
   model_info=[{k:model.get(k) for k in ['slug','default_reasoning_level','supported_reasoning_levels','context_window','auto_compact_token_limit','service_tiers','default_service_tier','supports_reasoning_summaries','supports_verbosity']}]
result={'settings':settings,'session_id':meta.get('id'),'session_file':str(selected),'context':contexts[-1] if contexts else None,'recent_usage':usage[-20:],'compactions':compact,'model_info':model_info,'panes':panes,'pane':pane}
if not AFTER:
 result.update(help=run(['/home/morse/.local/bin/codex','--help']),resume_help=run(['/home/morse/.local/bin/codex','resume','--help']),features=run(['/home/morse/.local/bin/codex','features','list']))
project_config=task/'project/.codex/config.toml'
result['project_settings_text']=project_config.read_text() if project_config.exists() else None
print(json.dumps(result))
'''.replace('AFTER',repr(args.after))
result=subprocess.run(['ssh','-o','BatchMode=yes','-o','StrictHostKeyChecking=yes','-o','ConnectTimeout=10','157.181.172.78','python3 -'],input=remote,capture_output=True,text=True,encoding='utf-8',timeout=80)
assert result.returncode==0,result.stderr
record=json.loads(result.stdout)
path=ROOT/'validation/.build'/('agent-efficiency-after.json' if args.after else 'agent-efficiency-before.json')
path.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
keys=['session_id','context','project_settings_text'] if args.after else ['settings','session_id','context','compactions','model_info','panes','pane','help','resume_help','features']
for key in keys:print(key,json.dumps(record[key]))
if args.after:
 before=json.loads((ROOT/'validation/.build/agent-efficiency-before.json').read_text(encoding='utf-8'))
 assert before['session_id']==record['session_id'],'Preserve the original session'
 assert record['context']['effort']=='medium'
 before_usage=before['recent_usage'][-1]['total'];after_usage=record['recent_usage'][-1]['total']
 recent={key:after_usage[key]-before_usage.get(key,0) for key in after_usage}
 record['usage_since_baseline']=recent
 record['cumulative_cached_input_fraction']=after_usage['cached_input_tokens']/after_usage['input_tokens']
 path.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
 print('Cached input fraction:',record['cumulative_cached_input_fraction'])
 print('New recorded usage:',json.dumps(recent))
else:print('USAGE',json.dumps(record['recent_usage'][-3:]))
