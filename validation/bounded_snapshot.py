"""Verify a completed bounded build without repeating its compilation."""
import json
from pathlib import Path
from bounded_build import CHAIN,COMMIT,digest,imports_of
from memory_budget import ROOT,require_budget

def verify_build(path: Path):
 require_budget()
 build=json.loads(path.read_text(encoding='utf-8'))
 assert build['passed'] and build['toolchain']==CHAIN and COMMIT in build['version']
 project=ROOT/'lean';closure=set();hashes={}
 def checked_digest(path):
  path=path.resolve()
  if path not in hashes:hashes[path]=digest(path)
  return hashes[path]
 def check(path,expected):
  assert checked_digest(ROOT/path)==expected,'Stale bounded build file: '+str(path)
 def visit(module):
  if module in closure:return
  closure.add(module)
  source=project/(module.replace('.','/')+'.lean')
  for dependency in imports_of(source.read_text(encoding='utf-8')):
   if dependency=='SmcTuring' or dependency.startswith('SmcTuring.'):visit(dependency)
 for module in build['targets']:visit(module)
 assert closure==set(build['modules']),'Build dependency closure differs'
 for module,record in build['modules'].items():
  relative=module.replace('.','/')
  check(project/(relative+'.lean'),record['source'])
  check(project/'.lake/proof-build/ir'/(relative+'.setup.json'),record['setup_sha256'])
  assert any(path.endswith(relative+'.olean') for path in record['artifacts']),module
  for path,expected in record['artifacts'].items():check(path,expected)
 for group in ['context','import_header_sources']:
  for path,expected in build[group].items():check(path,expected)
 for files in build['external_artifacts'].values():
  for path,expected in files.items():check(path,expected)
 return build
