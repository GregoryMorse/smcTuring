"""Run existing native validators serially under their unchanged Windows guard."""
import json, os, subprocess, sys
from datetime import date
from pathlib import Path
from common import ROOT, digest, inputs, verify_sources, require_ci, write

SUITES = [
 ('run_baseline.py','baseline.json'),('run_defaddr.py','defaddr.json'),
 ('run_pure.py','pure.json'),('audit_encoding.py','encoding.json'),
 ('run_branch.py','branch.json'),('run_branch_geometries.py','branch_geometries.json'),
 ('run_half_frame.py','half-frame.json'),('run_multiplication.py','multiplication.json'),
 ('run_constant.py','constant.json'),('run_zero.py','zero.json'),
 ('run_conversion.py','conversion.json'),('run_template.py','template.json'),
 ('run_transfer.py','transfer.json'),('run_division.py','division.json'),
 ('run_terminal.py','terminal.json'),('run_accumulator.py','accumulator.json'),
 ('run_input_operand.py','input_operand.json'),('run_dword_owner.py','dword_owner.json'),
 ('run_dword_comparison.py','dword_comparison.json'),('run_cursor.py','cursor.json'),
 ('run_input_update.py','input_update.json')]

def check_hashes(value):
    # Every report's nested path -> SHA256 map is independently rechecked.
    if isinstance(value,dict):
        for name, expected in value.items():
            if isinstance(expected,str) and len(expected)==64 and all(c in '0123456789abcdef' for c in expected) and (ROOT/name).is_file():
                assert digest(ROOT/name)==expected, 'Stale native artifact: '+name
            check_hashes(expected)
    elif isinstance(value,list):
        for item in value: check_hashes(item)

def main():
    require_ci()
    assert os.name=='nt'
    before=inputs()
    proof=json.loads((ROOT/'validation/lean.json').read_text())
    assert proof['passed']
    verify_sources(proof['sources'])
    # Fresh report creation is mandatory; checked-in historical success is not CI evidence.
    for _,name in SUITES:
        (ROOT/'validation'/name).unlink(missing_ok=True)
    results=[]
    subprocess.run([sys.executable,str(ROOT/'validation/limited_run.py'),sys.executable,str(ROOT/'validation/ci/windows_tools.py')],cwd=ROOT,check=True)
    for script,name in SUITES:
        args=['--as-of',date.today().isoformat()] if script=='run_baseline.py' else []
        command=[sys.executable,str(ROOT/'validation/limited_run.py'),sys.executable,str(ROOT/'validation'/script),*args]
        subprocess.run(command,cwd=ROOT,check=True,timeout=3600)
        path=ROOT/'validation'/name
        result=json.loads(path.read_text())
        if 'passed' in result: assert result['passed'] is True, name
        else: assert result.get('runs') and all(run['passed'] for run in result['runs']), name
        if name=='baseline.json':
            assert {r['configuration'] for r in result['runs']}=={'Debug-Win32','Release-Win32','Debug-x64','Release-x64'}
            assert sum(r['simulator_count'] for r in result['runs'])==30
        check_hashes(result)
        results.append(dict(script=script,report=path.relative_to(ROOT).as_posix(),sha256=digest(path),passed=True))
    assert before==inputs(), 'Native validation changed an input'
    artifacts={p.relative_to(ROOT).as_posix():digest(p) for p in (ROOT/'validation/.build').rglob('*') if p.is_file()}
    write(ROOT/'validation/ci-results/native-artifacts.json',dict(passed=True,scope='Actual Windows baseline plus corrected x86/x64 native/MASM/loaded-image/COFF suites; x86-only printed multiply/constant retained',
          commit=os.environ['GITHUB_SHA'],run_id=os.environ['GITHUB_RUN_ID'],repository=os.environ['GITHUB_REPOSITORY'],
          sources=before,linux_report_sha256=proof['linux_report_sha256'],suites=results,artifacts=artifacts,
          full_windows_lean_audit_claimed=False,native_job_cap_bytes=1500000000))

if __name__=='__main__': main()
