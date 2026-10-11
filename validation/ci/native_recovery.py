"""Finish errata/native acceptance for the unchanged, already compiled public proof."""
import argparse, json, os, shutil, subprocess, sys
from pathlib import Path

SOURCE_COMMIT = '1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4'
PRIOR_RUN = '38108181056'
PROOF_SHA = '078d3b80124d05e98ca2dcaa9e52cb105c087e89b4350dc696c9f9187b5baf2d'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['linux', 'windows'])
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--prior', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    driver = Path(__file__).resolve().parents[2]
    assert os.environ.get('GITHUB_ACTIONS') == 'true'
    actual = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == SOURCE_COMMIT
    env = dict(os.environ, GITHUB_SHA=SOURCE_COMMIT, SMCTURING_SOURCE_ROOT=str(source),
               PYTHONPATH=str(driver/'validation'))
    sys.path.insert(0, str(driver/'validation'))
    os.environ['SMCTURING_SOURCE_ROOT'] = str(source)
    from checkpoint_common import audit_gate, digest
    def run(script, *extra):
        subprocess.run([sys.executable, str(source/'validation'/script), *map(str, extra)],
                       cwd=source, env=env, check=True)
    if args.phase == 'linux':
        assert args.prior is not None
        prior = args.prior.resolve()
        original = prior/'remote-evidence/lean.json'
        assert digest(original) == PROOF_SHA
        report = json.loads(original.read_text(encoding='utf-8'))
        assert report['passed'] and len(report['modules']) == 1152 and len(report['declarations']) == 7976
        assert report['kernel_compiled'] == 1152 and report['verified_reused'] == 0
        assert all(set(d['axioms']) <= {'propext', 'Quot.sound', 'Classical.choice'} for d in report['declarations'])
        # Copy reports/logs only. Linux compiled objects never become Windows objects.
        target = source/'validation/remote-evidence'
        target.mkdir(parents=True, exist_ok=True)
        for name in ['lean.json', 'axiom-audit.log', 'resource.json']:
            shutil.copyfile(prior/'remote-evidence'/name, target/name)
        audit_gate()  # Every original source hash and the complete declaration list must still match.
        pins = json.loads((source/'validation/ci/pins.json').read_text(encoding='utf-8'))
        for ref in pins['reference_files']:
            packaged = source/ref['packaged_path']
            assert digest(packaged) == ref['sha256']
            destination = source/ref['path']
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(packaged, destination)
        run('audit_errata.py', '--remote-source-proof')
        run('ci/linux_finish.py')
        snapshot_path = source/'validation/ci-results/linux-snapshot.json'
        snapshot = json.loads(snapshot_path.read_text(encoding='utf-8'))
        snapshot['proof_origin'] = dict(run_id=PRIOR_RUN, commit=SOURCE_COMMIT, report_sha256=PROOF_SHA,
            audit_passed_before_errata_packaging_failure=True, current_run_compiled_modules=0,
            unchanged_modules_verified=1152, original_report_preserved=True)
        snapshot['workflow_caller_commit'] = os.environ.get('GITHUB_SHA')
        snapshot['runtime_audit_provider'] = dict(path='validation/checkpoint_common.py', sha256=digest(driver/'validation/checkpoint_common.py'))
        snapshot_path.write_text(json.dumps(snapshot, indent=2)+'\n', encoding='utf-8')
        print('Unchanged complete public proof audit retained; errata and Linux snapshot passed. No theorem rebuilt.', flush=True)
    else:
        assert os.name == 'nt'
        linux = source/'linux-evidence'
        assert digest(linux/'remote-evidence/lean.json') == PROOF_SHA
        run('ci/bootstrap.py')
        run('ci/windows_exports.py')
        run('ci/proof_bridge.py', linux/'remote-evidence/lean.json', linux/'ci-results/linux-snapshot.json')
        run('ci/windows_native.py')
        print('Fresh Windows exporter objects and all native suites passed for the same public proof source.', flush=True)

if __name__ == '__main__':
    main()
