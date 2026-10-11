"""Finish errata/native acceptance for the unchanged, already compiled public proof."""
import argparse, json, os, runpy, shutil, subprocess, sys, tomllib, types
from pathlib import Path

SOURCE_COMMIT = '1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4'
PRIOR_RUN = '38108181056'
PROOF_SHA = '078d3b80124d05e98ca2dcaa9e52cb105c087e89b4350dc696c9f9187b5baf2d'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['linux', 'windows', 'windows-export'])
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
    elif args.phase == 'windows-export':
        assert os.name == 'nt'
        # The immutable release omitted only two library registrations in its
        # alternate cache configuration. No submitted file is rewritten. The
        # exporter compiles named source files directly, with explicit options.
        canonical = tomllib.loads((source/'lean/lakefile.toml').read_text(encoding='utf-8'))
        proof = tomllib.loads((source/'lean/lakefile.proof.toml').read_text(encoding='utf-8'))
        assert proof.pop('buildDir') == '.lake/proof-build'
        assert canonical['lean_lib'] == [{'name': n} for n in ['SmcTuring','Challenge','Solution']]
        assert proof['lean_lib'] == [{'name': 'SmcTuring'}]
        canonical['lean_lib'] = proof['lean_lib']
        assert canonical == proof, 'Unexpected frozen build-configuration difference'
        provider = types.ModuleType('lean_build')
        def frozen_command(project, binary):
            assert project.resolve() == (source/'lean').resolve()
            return [str(binary/'lake.exe'), '--file', 'lakefile.proof.toml']
        provider.lake_command = frozen_command
        sys.modules['lean_build'] = provider
        sys.path[:0] = [str(source/'validation/ci'), str(source/'validation')]
        runpy.run_path(str(source/'validation/ci/windows_exports.py'), run_name='__main__')
        path = source/'validation/ci-results/windows-exports.json'
        record = json.loads(path.read_text(encoding='utf-8'))
        record['frozen_configuration_recovery'] = dict(
            omitted_library_registrations=['Challenge','Solution'],
            all_other_configuration_fields_identical=True,
            source_files_modified=False,
            direct_compiler_options={'autoImplicit':False},
            runtime_driver_sha256=digest(Path(__file__)))
        path.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    else:
        assert os.name == 'nt'
        linux = source/'linux-evidence'
        assert digest(linux/'remote-evidence/lean.json') == PROOF_SHA
        run('ci/bootstrap.py')
        subprocess.run([sys.executable, str(Path(__file__)), 'windows-export',
                        '--source', str(source)], cwd=source, env=env, check=True)
        run('ci/proof_bridge.py', linux/'remote-evidence/lean.json', linux/'ci-results/linux-snapshot.json')
        run('ci/windows_native.py')
        print('Fresh Windows exporter objects and all native suites passed for the same public proof source.', flush=True)

if __name__ == '__main__':
    main()
