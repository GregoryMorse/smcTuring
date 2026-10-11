"""Expose checked Linux declaration groups to native tests, without Windows proof claims."""
import argparse, json, os, re
from pathlib import Path
from common import ROOT, CHAIN, COMMIT, ALLOWED, digest, inputs, verify_sources, write

def bridge(report_path, snapshot_path):
    report = json.loads(Path(report_path).read_text(encoding='utf-8'))
    snapshot = json.loads(Path(snapshot_path).read_text(encoding='utf-8'))
    assert report['passed'] and report['commit']==COMMIT and report['toolchain']==CHAIN
    assert snapshot['proof_report_sha256']==digest(report_path)
    if os.environ.get('GITHUB_ACTIONS')=='true':
        assert snapshot['commit']==os.environ['GITHUB_SHA'], 'Proof/native commits differ'
        assert snapshot['run_id']==os.environ['GITHUB_RUN_ID'], 'Proof/native runs differ'
    assert snapshot['sources']==inputs(), 'CI jobs do not have the same complete source snapshot'
    assert {n for n in report['sources'] if n.endswith('.lean')}=={n for n in snapshot['sources'] if n.endswith('.lean')}, 'Incomplete Lean source binding'
    verify_sources(report['sources'])
    expected = re.findall(r'^#print axioms (\S+)',(ROOT/'lean/Audit.lean').read_text(encoding='utf-8'),re.M)
    declarations = report['declarations']
    assert [d['name'] for d in declarations]==expected and len(expected)==len(set(expected))
    assert all(set(d['axioms'])<=ALLOWED for d in declarations)
    names = set(expected)
    sources = dict(snapshot['sources'])
    if os.name == 'nt':
        # Legacy native validators use str(relative Windows Path). Keep the
        # canonical manifest and add aliases for the identical checked files.
        sources.update({str(Path(name)):sha for name,sha in snapshot['sources'].items()})
    contract = json.loads(Path(__file__).with_name('native-proof-contract.json').read_text(encoding='utf-8'))
    for group, required in contract['required_declaration_groups'].items():
        assert set(required)<=names, 'Missing positively audited native group: '+group
    result = dict(passed=True,scope='Complete Linux kernel/axiom evidence adapted for native test declaration lookup; NOT a Windows proof audit',
                  toolchain=CHAIN,commit=COMMIT,version=report['version'],sources=sources,declarations=declarations,
                  linux_report_sha256=digest(report_path),**contract['required_declaration_groups'],**contract['flags'])
    write(ROOT/'validation/lean.json',result)
    for stem, audit in [('cursor','AuditCursor.lean'),('input_update','AuditInputUpdate.lean')]:
        required = set(re.findall(r'^#print axioms (\S+)',(ROOT/'lean'/audit).read_text(encoding='utf-8'),re.M))
        assert required<=names
        write(ROOT/f'validation/{stem}_lean.json',dict(passed=True,scope='Linux complete audit subset for Windows native lookup; NOT a Windows proof audit',
              toolchain=CHAIN,commit=COMMIT,sources=sources,declarations=[d for d in declarations if d['name'] in required],linux_report_sha256=digest(report_path)))

def main():
    p=argparse.ArgumentParser();p.add_argument('report');p.add_argument('snapshot');args=p.parse_args()
    bridge(args.report,args.snapshot)

if __name__ == '__main__': main()
