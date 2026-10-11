"""Strict reuse of kernel-compiled modules from a source-bound passing audit.

Cache hits never replace the current declaration/axiom audit. Legacy reports
are accepted only with their matching audit log and compiler record.
"""
import hashlib, json
from pathlib import Path

STANDARD_AXIOMS={'propext','Classical.choice','Quot.sound'}
CONFIG_INPUTS=('lean/lean-toolchain','lean/lakefile.proof.toml',
               'lean/lake-manifest.json','validation/remote_artifacts.py')

def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as stream:
  for block in iter(lambda:stream.read(1<<20),b''):h.update(block)
 return h.hexdigest()

def input_fingerprint(inputs):
 return hashlib.sha256(json.dumps(inputs,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def read_previous(evidence,context,sources):
 try:
  report=json.loads((evidence/'lean.json').read_text())
  compiler=json.loads((evidence/'toolchain.json').read_text())
  assert report['passed'] is True
  assert report['version']==context['version']==compiler['version']
  assert report['toolchain']==compiler['toolchain']==context['toolchain']
  assert report['commit']==context['commit']
  assert compiler['binary_sha256']==context['compiler_sha256']
  assert report['audit_sha256']==digest(evidence/'axiom-audit.log')
  assert report['declarations']
  assert all(set(item['axioms'])<=STANDARD_AXIOMS for item in report['declarations'])
  assert all(report['sources'].get(name)==sources[name] for name in CONFIG_INPUTS)
  if 'cache_context' in report:assert report['cache_context']==context
  return report
 except (AssertionError,OSError,ValueError,KeyError,TypeError):return {}

def reusable(previous,name,source,command,setup_sha256,inputs,outputs,force=False):
 if force:return False
 record=previous.get('modules',{}).get(name,{})
 if not outputs or not any(path.endswith('.olean') for path in outputs):return False
 if any(record.get(key)!=value for key,value in (
    ('source',source),('command',command),('setup_sha256',setup_sha256),('artifacts',outputs))):return False
 if 'input_artifacts_sha256' in record:return record['input_artifacts_sha256']==input_fingerprint(inputs)
 # Migration from the original complete-audit format: the setup hash fixes
 # the selected artifact paths; the complete report binds their old hashes.
 old_inputs=previous.get('imported_artifacts',{})
 return bool(inputs) and all(old_inputs.get(path)==sha for path,sha in inputs.items())
