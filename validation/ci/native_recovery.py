"""Finish errata/native acceptance for the unchanged, already compiled public proof."""
import argparse, importlib.util, json, os, runpy, shutil, subprocess, sys, tomllib, types
from pathlib import Path

SOURCE_COMMIT = '1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4'
PRIOR_RUN = '38108181056'
PROOF_SHA = '078d3b80124d05e98ca2dcaa9e52cb105c087e89b4350dc696c9f9187b5baf2d'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['linux', 'windows', 'windows-export', 'windows-native'])
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--prior', type=Path)
    parser.add_argument('--windows-prior', type=Path)
    parser.add_argument('--native-prior', type=Path)
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
    elif args.phase == 'windows-native':
        assert os.name == 'nt' and os.environ.get('SMCTURING_MSBUILD_TOOLSET') == 'v143'
        sys.path[:0] = [str(source/'validation/ci'), str(source/'validation')]
        path = source/'validation/ci/windows_native.py'
        spec = importlib.util.spec_from_file_location('frozen_native',path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        retained = []
        prior = args.native_prior.resolve() if args.native_prior is not None else None
        if prior is not None:
            prior_proof = json.loads((prior/'lean.json').read_text(encoding='utf-8'))
            assert prior_proof['linux_report_sha256'] == PROOF_SHA
            assert prior_proof['sources'] == module.inputs()
            shutil.copytree(prior/'.build',source/'validation/.build',dirs_exist_ok=True)
            shutil.copyfile(prior/'kernel.json',source/'validation/kernel.json')
            for script,name in module.SUITES[:6]:
                path = prior/name
                result = json.loads(path.read_text(encoding='utf-8'))
                assert result.get('passed',all(r['passed'] for r in result.get('runs',[])))
                if name=='baseline.json':
                    assert len(result['runs'])==4 and sum(r['simulator_count'] for r in result['runs'])==30
                    for row in result['runs']:
                        assert digest(prior/'.build/baseline'/row['configuration']/'smcTuring.exe')==row['executable_sha256']
                module.verify_sources(result.get('sources',{}))
                def retained_hashes(value):
                    if isinstance(value,dict):
                        for name,expected in value.items():
                            if isinstance(expected,str) and len(expected)==64 and all(c in '0123456789abcdef' for c in expected):
                                relative = Path(name)
                                if relative.parts and relative.parts[0]=='validation' and '.build' in relative.parts:
                                    saved = prior/relative.relative_to('validation')
                                    assert digest(saved) == expected
                            retained_hashes(expected)
                    elif isinstance(value,list):
                        for item in value:retained_hashes(item)
                retained_hashes(result)
                shutil.copyfile(path,source/'validation'/name)
                retained.append(dict(script=script,report='validation/'+name,sha256=digest(path),passed=True,
                    origin_run_id='38117226865',verified_retained=True))
            shutil.copyfile(prior/'kernel.json',source/'validation/kernel.json')
            module.SUITES = module.SUITES[6:]
        def native_run(command, **kwargs):
            command = list(command)
            baseline = str(source/'validation/run_baseline.py')
            if baseline in command:
                command[command.index(baseline)] = str(driver/'validation/run_baseline.py')
            return subprocess.run(command, **kwargs)
        module.subprocess = types.SimpleNamespace(run=native_run)
        module.main()
        path = source/'validation/ci-results/native-artifacts.json'
        result = json.loads(path.read_text(encoding='utf-8'))
        if retained:
            previous_tools = json.loads((prior/'ci-results/windows-tools.json').read_text(encoding='utf-8'))['tools']
            current_tools = json.loads((source/'validation/ci-results/windows-tools.json').read_text(encoding='utf-8'))['tools']
            assert {n:v['sha256'] for n,v in previous_tools.items()} == {n:v['sha256'] for n,v in current_tools.items()}
            result['suites'] = retained + result['suites']
            result['retained_native_origin'] = dict(run_id='38117226865',passed_suites=6,new_suites=15,
                exact_source_snapshot_verified=True,tool_binary_hashes_match=True)
        result['runtime_baseline_provider'] = dict(source_files_modified=False,
            path='validation/run_baseline.py',sha256=digest(driver/'validation/run_baseline.py'),
            project_requested_toolset='v145',runner_override_toolset='v143')
        result['runtime_proof_bridge_provider'] = dict(source_files_modified=False,
            path='validation/ci/proof_bridge.py',sha256=digest(driver/'validation/ci/proof_bridge.py'),
            windows_path_aliases_for_identical_checked_files=True)
        path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:
        assert os.name == 'nt'
        linux = source/'linux-evidence'
        assert digest(linux/'remote-evidence/lean.json') == PROOF_SHA
        # Check cross-platform checkout identity before installing or compiling.
        sys.path.insert(0, str(source/'validation/ci'))
        from common import inputs
        snapshot = json.loads((linux/'ci-results/linux-snapshot.json').read_text(encoding='utf-8'))
        current = inputs()
        differences = {n:dict(linux=snapshot['sources'].get(n),windows=current.get(n))
                       for n in snapshot['sources'].keys() | current.keys()
                       if snapshot['sources'].get(n) != current.get(n)}
        assert not differences, 'Source checkout mismatch: '+json.dumps(differences,sort_keys=True)
        print('Exact Linux/Windows checkout identity passed before bootstrap.',flush=True)
        run('ci/bootstrap.py')
        if args.windows_prior is not None:
            previous_path = args.windows_prior.resolve()/'ci-results/windows-exports.json'
            previous_sha = digest(previous_path)
            assert previous_sha == 'e45782301b7bae44a269d809a5fb33995e61dbd655b8ec710a42267afed8cbd6'
            previous = json.loads(previous_path.read_text(encoding='utf-8'))
            assert previous['passed'] and len(previous['modules']) == 210
            assert previous['frozen_configuration_recovery']['source_files_modified'] is False
            sys.path.insert(0, str(source/'validation'))
            from module_artifacts import TOOLCHAIN
            assert previous['compiler_sha256'] == digest(TOOLCHAIN/'bin/lean.exe')
            checked = {}
            def checked_hash(name, expected):
                path = source/name
                assert path.resolve().is_relative_to(source)
                if name not in checked: checked[name] = digest(path)
                assert checked[name] == expected, 'Windows cache mismatch: '+name
            for name, record in previous['modules'].items():
                relative = Path(*name.split('.'))
                checked_hash((Path('lean')/relative.with_suffix('.lean')).as_posix(),record['source'])
                checked_hash((Path('lean/.lake/proof-build/ir')/relative.with_suffix('.setup.json')).as_posix(),record['setup'])
                for group in ['artifacts','dependencies']:
                    for path, expected in record[group].items(): checked_hash(path,expected)
            previous['verification_origin'] = dict(run_id='38115827274',source_commit=SOURCE_COMMIT,
                report_sha256=previous_sha,prior_freshly_compiled=210,current_freshly_compiled=0,
                verified_reused=210,unique_artifact_hashes_verified=len(checked))
            previous['scope'] = 'Unchanged Windows exporter cache, fully hash-verified against prior fresh Windows build; no project module recompiled'
            path = source/'validation/ci-results/windows-exports.json'
            path.write_text(json.dumps(previous,indent=2)+'\n',encoding='utf-8')
            print('All 210 previously compiled Windows exporter modules and their dependency/setup/source hashes verified; no module rebuilt.',flush=True)
            del previous, checked
        else:
            subprocess.run([sys.executable, str(Path(__file__)), 'windows-export',
                            '--source', str(source)], cwd=source, env=env, check=True)
        subprocess.run([sys.executable,str(driver/'validation/ci/proof_bridge.py'),
                        str(linux/'remote-evidence/lean.json'),str(linux/'ci-results/linux-snapshot.json')],
                       cwd=source,env=env,check=True)
        command = [sys.executable,str(Path(__file__)),'windows-native','--source',str(source)]
        if args.native_prior is not None:command+=['--native-prior',str(args.native_prior.resolve())]
        subprocess.run(command,cwd=source,env=env,check=True)
        print('Verified Windows exporter objects and all native suites passed for the same public proof source.', flush=True)

if __name__ == '__main__':
    main()
