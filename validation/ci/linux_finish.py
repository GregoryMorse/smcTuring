"""Bind a finished complete Linux audit to the CI source snapshot and GitHub identity."""
import json, os
from common import ROOT, inputs, verify_sources, digest, write

def main():
    path=ROOT/'validation/remote-evidence/lean.json'
    report=json.loads(path.read_text())
    assert report['passed']
    verify_sources(report['sources'])
    errata_path=ROOT/'validation/remote-evidence/errata-source-proof.json'
    errata=json.loads(errata_path.read_text())
    assert errata['passed'] and errata['source_excerpts_checked']==60 and errata['pages']==2
    write(ROOT/'validation/ci-results/linux-snapshot.json',dict(passed=True,proof_report_sha256=digest(path),sources=inputs(),
          commit=os.environ.get('GITHUB_SHA'),run_id=os.environ.get('GITHUB_RUN_ID'),repository=os.environ.get('GITHUB_REPOSITORY'),
          modules=len(report['modules']),declarations=len(report['declarations']),force_replay=report['force_replay'],
          errata_report_sha256=digest(errata_path)))

if __name__ == '__main__': main()
