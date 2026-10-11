"""Select rc3 module artifacts using its documented import-level rules."""
import json,re
from pathlib import Path
from memory_budget import ROOT
PROJECT=ROOT/'lean'
CHAIN='leanprover/lean4:v4.35.0-rc3'
TOOLCHAIN=PROJECT/'.elan/toolchains'/CHAIN.replace('/','--').replace(':','---')

def strip_comments(text):
 result=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;result.append('  ');i+=2
  elif depth and text.startswith('-/',i):depth-=1;result.append('  ');i+=2
  elif not depth and text.startswith('--',i):
   end=text.find('\n',i)
   if end<0:break
   result.append('\n');i=end+1
  else:
   result.append('\n' if text[i]=='\n' else (' ' if depth else text[i]));i+=1
 return ''.join(result)

class ArtifactResolver:
 def __init__(self):
  manifest=json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf-8'))
  self.locations=[(PROJECT,PROJECT/'.lake/proof-build/lib/lean')]
  self.locations += [(PROJECT/'.lake/packages'/p['name'],PROJECT/'.lake/packages'/p['name']/'.lake/build/lib/lean') for p in reversed(manifest['packages'])]
  self.locations += [(TOOLCHAIN/'src/lean',TOOLCHAIN/'lib/lean'),(TOOLCHAIN/'src/lean/lake',TOOLCHAIN/'lib/lean')]
  self.headers={};self.paths={};self.sources={}
 def locate(self,name):
  if name in self.paths:return self.paths[name]
  relative=Path(*name.split('.'))
  for sources,objects in self.locations:
   source=(sources/relative).with_suffix('.lean')
   obj=(objects/relative).with_suffix('.olean')
   if source.is_file() and (obj.is_file() or name==getattr(self,'root',None)):
    self.paths[name]=(source,obj);return source,obj
  raise FileNotFoundError('Missing source/object for imported module '+name)
 def header(self,name):
  if name in self.headers:return self.headers[name]
  source,_=self.locate(name)
  text=strip_comments(source.read_text(encoding='utf-8-sig'))
  header=[];prelude=False;is_module=False
  for line in text.splitlines():
   line=line.strip()
   if not line:continue
   if line=='module':is_module=True;continue
   if line=='prelude':prelude=True;continue
   match=re.fullmatch(r'(?P<mods>(?:(?:public|meta)\s+)*)import\s+(?P<all>all\s+)?(?P<names>[A-Za-z0-9_.\s]+)',line)
   if match:
    mods=match['mods'].split()
    for item in match['names'].split():
     header.append((item,'public' in mods,bool(match['all']),'meta' in mods))
    continue
   break
  if not is_module:raise RuntimeError('Legacy module cannot be silently narrowed: '+name)
  if not prelude:header.insert(0,('Init',True,False,False))
  self.headers[name]=header;self.sources[name]=source
  return header
 def select(self,root):
  # Each state is (needsData, importAll, needsIRTrans), as importModulesCore.
  self.root=root
  states={};pending=[(root,True,True,False)]
  while pending:
   name,data,all_,meta=pending.pop()
   old=states.get(name,(False,False,False))
   current=tuple(a or b for a,b in zip(old,(data,all_,meta)))
   if name in states and current==old:continue
   states[name]=current
   for child,public,child_all,child_meta in self.header(name):
    child_data=current[0] and (public or current[1])
    child_all=current[1] and child_all
    child_meta=current[2] or (child_data and child_meta)
    if child_data or child_all or child_meta:pending.append((child,child_data,child_all,child_meta))
  maps={}
  for name,(data,all_,meta) in states.items():
   if name==root:continue
   _,obj=self.locate(name);stem=obj.with_suffix('')
   oleans=[str(obj)]
   server=Path(str(stem)+'.olean.server')
   if server.exists():oleans.append(str(server))
   if all_:
    private=Path(str(stem)+'.olean.private')
    if not private.exists():raise FileNotFoundError('Required private data missing: '+name)
    oleans.append(str(private))
   ir=[str(Path(str(stem)+suffix)) for suffix in ['.ir.sig','.ir'] if Path(str(stem)+suffix).exists()]
   maps[name]=[oleans,ir]
  return maps,states
