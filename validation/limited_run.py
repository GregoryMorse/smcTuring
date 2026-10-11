"""Run one command under the user's strict aggregate memory ceiling."""
import argparse,json,os,subprocess,sys,time
from pathlib import Path
from memory_budget import Budget,ResidentMonitor,MAX_BYTES,ROOT

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 parser=argparse.ArgumentParser()
 parser.add_argument('--max-bytes',type=int,default=MAX_BYTES)
 parser.add_argument('--timeout',type=int,default=1800)
 parser.add_argument('--cwd',default=str(ROOT))
 parser.add_argument('--output')
 parser.add_argument('--report',default=str(ROOT/'validation/.build/memory-latest.json'))
 parser.add_argument('command',nargs=argparse.REMAINDER)
 args=parser.parse_args();command=args.command
 if command[:1]==['--']:command=command[1:]
 if not command:parser.error('missing command after --')
 manifest=json.loads((ROOT/'lean/lake-manifest.json').read_text(encoding='utf-8'))
 package_paths=[str(ROOT/'lean/.lake/packages'/p['name']/'.lake/build/lib/lean') for p in reversed(manifest['packages'])]
 os.environ['LEAN_PATH']=';'.join(package_paths+[str(ROOT/'lean/.lake/proof-build/lib/lean')])
 if Path(command[0]).name.lower()=='lean.exe':command=[command[0],'-M768','-j1']+command[1:]
 budget=Budget(args.max_bytes);monitor=ResidentMonitor(budget);start=time.monotonic();code=1
 target=None;launcher_error=None
 try:
  monitor.start()
  if args.output:
   path=Path(args.output);path.parent.mkdir(parents=True,exist_ok=True);target=path.open('wb')
  result=subprocess.run(command,cwd=args.cwd,stdout=target if target else subprocess.PIPE,stderr=subprocess.STDOUT,
   timeout=args.timeout,creationflags=subprocess.CREATE_NO_WINDOW)
  code=result.returncode
  if monitor.error:code=137
  if not target and result.stdout:print(result.stdout.decode("utf-8",errors="replace"),end="",flush=True)
 except BaseException as exc:
  launcher_error=type(exc).__name__+': '+str(exc)
  if code==0:code=1
  raise
 finally:
  if target:target.close()
  report=budget.report();report.update(monitor.finish())
  if monitor.error:code=137
  report.update(command=command,exit=code,launcher_error=launcher_error,elapsed_seconds=round(time.monotonic()-start,3))
  destination=Path(args.report);destination.parent.mkdir(parents=True,exist_ok=True)
  destination.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
  print('Memory cap: '+str(report['memory_limit_bytes'])+' bytes; peak group commit: '+str(report['peak_group_commit_bytes'])+' bytes; sampled peak resident: '+str(report['sampled_peak_group_resident_bytes'])+' bytes; exit '+str(code),flush=True)
  budget.release()
 raise SystemExit(code)
if __name__=='__main__':main()
