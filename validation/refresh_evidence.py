"""Orchestrate sequential verification; every check runs in limited_run's job."""
import argparse,json,shutil,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PHASES=[
 ('python-syntax','check_python_syntax.py',[]),
 ('guard-current','check_memory_budget.py',[]),
 ('lean-current','run_lean.py',['--build-report','validation/.build/full-bounded-build.json']),
 ('cursor-local','run_cursor_lean.py',[]),
 ('input-update-local','run_input_update_lean.py',[]),
 ('pure-native','run_pure.py',[]),
 ('half-frame-native','run_half_frame.py',[]),
 ('branch-native','run_branch.py',[]),
 ('multiplication-native','run_multiplication.py',[]),
 ('constant-native','run_constant.py',[]),
 ('zero-native','run_zero.py',[]),
 ('conversion-native','run_conversion.py',[]),
 ('template-native','run_template.py',[]),
 ('transfer-native','run_transfer.py',[]),
 ('division-native','run_division.py',[]),
 ('branch-geometries-native','run_branch_geometries.py',[]),
 ('terminal-native','run_terminal.py',[]),
 ('accumulator-native','run_accumulator.py',[]),
 ('input-operand-native','run_input_operand.py',[]),
 ('dword-owner-native','run_dword_owner.py',[]),
 ('dword-comparison-native','run_dword_comparison.py',[]),
 ('cursor-native','run_cursor.py',[]),
 ('input-update-native','run_input_update.py',[]),
 ('encoding-current','audit_encoding.py',[]),
 ('errata-current','audit_errata.py',[]),
 ('evidence-current','audit_evidence.py',[])]

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 parser=argparse.ArgumentParser()
 parser.add_argument('--start',choices=[phase[0] for phase in PHASES])
 parser.add_argument('--stop',choices=[phase[0] for phase in PHASES])
 args=parser.parse_args()
 begin=next((i for i,p in enumerate(PHASES) if p[0]==args.start),0)
 end=next((i+1 for i,p in enumerate(PHASES) if p[0]==args.stop),len(PHASES))
 assert begin<end,'Empty phase range'
 records=[];destination=ROOT/'validation/.build/refresh-progress.json'
 history=ROOT/'validation/.build/refresh-history'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 history.mkdir(parents=True,exist_ok=False)
 for name,script,arguments in PHASES[begin:end]:
  output='validation/.build/refresh-'+name+'.log'
  resource='validation/.build/memory-'+name+'.json'
  command=[sys.executable,'validation/limited_run.py','--timeout','1800',
   '--output',output,'--report',resource,'--',sys.executable,'validation/'+script]+arguments
  print('Starting '+name,flush=True);started=time.monotonic()
  result=subprocess.run(command,cwd=ROOT)
  checkpoint=history/name;checkpoint.mkdir()
  for relative in [output,resource]:
   source=ROOT/relative
   if source.is_file():shutil.copy2(source,checkpoint/source.name)
  records.append(dict(phase=name,command=command,exit=result.returncode,
   output=output,memory_report=resource,elapsed_seconds=round(time.monotonic()-started,3)))
  destination.write_text(json.dumps(dict(phases=records),indent=2)+'\n',encoding='utf-8')
  shutil.copy2(destination,history/destination.name)
  if result.returncode:raise SystemExit('Verification failed: '+name+'; inspect '+output)
  print('Passed '+name,flush=True)
 print('Requested sequential verification phases passed.',flush=True)
if __name__=='__main__':main()
