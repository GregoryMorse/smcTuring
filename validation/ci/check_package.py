"""Offline package gate: syntax, pins, registry coverage, closure and fail-closed scope."""
import ast, json, re, tomllib
from pathlib import Path
from common import ROOT, COMMIT, digest, inputs, write

def main():
    checks={}
    scripts=sorted(Path(__file__).parent.glob('*.py'))
    for source in scripts: ast.parse(source.read_text(encoding='utf-8'))
    checks['python_syntax']=len(scripts)
    pins=json.loads(Path(__file__).with_name('pins.json').read_text(encoding='utf-8'))
    manifest=json.loads((ROOT/'lean/lake-manifest.json').read_text(encoding='utf-8'))
    assert next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib') == pins['mathlib_revision']
    for name in ['lakefile.toml','lakefile.proof.toml']:
        config=tomllib.loads((ROOT/'lean'/name).read_text(encoding='utf-8'))
        assert next(p['rev'] for p in config['require'] if p['name']=='mathlib') == pins['mathlib_revision']
    checks['mathlib_pins_consistent']=True
    for platform in ['linux','windows']:
        assert pins[platform]['browser_download_url'].startswith('https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/')
        assert re.fullmatch(r'sha256:[0-9a-f]{64}',pins[platform]['digest'])
    checks['local_reference_matches']={}
    for ref in pins['reference_files']:
        assert digest(ROOT/ref['packaged_path'])==ref['sha256'], ref['packaged_path']
        # Fresh CI bootstrap installs these pinned bytes. Locally rebuilt
        # PDF/log metadata may differ; record that separately from package validity.
        local=ROOT/ref['path']
        checks['local_reference_matches'][ref['path']]=local.is_file() and digest(local)==ref['sha256']
    checks['release_and_reference_pins']=True
    expected=re.findall(r'^#print axioms (\S+)',(ROOT/'lean/Audit.lean').read_text(encoding='utf-8'),re.M)
    contract=json.loads(Path(__file__).with_name('native-proof-contract.json').read_text(encoding='utf-8'))
    assert all(set(v)<=set(expected) for v in contract['required_declaration_groups'].values())
    assert all(contract['flags'].values())
    checks['native_groups_covered']=len(contract['required_declaration_groups'])
    # Walk actual imports before any Windows build. Never silently add the whole umbrella.
    def imports_of(text):
        return [name for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)',text,re.M)
                for name in line.split('--',1)[0].split()]
    roots={n for p in (ROOT/'lean').glob('Export*.lean') for n in imports_of(p.read_text(encoding='utf-8')) if n.startswith('SmcTuring')}
    assert 'SmcTuring' not in roots
    closure=set()
    def visit(name):
        if name in closure:return
        closure.add(name)
        source=ROOT/'lean'/Path(*name.split('.')).with_suffix('.lean')
        assert source.is_file()
        for dep in imports_of(source.read_text(encoding='utf-8')):
            if dep.startswith('SmcTuring'):visit(dep)
    for name in roots:visit(name)
    checks['windows_exporter_roots']=len(roots)
    checks['windows_exporter_closure']=len(closure)
    # Both Windows-only entrypoints must actually refuse execution here.
    from common import require_ci
    try: require_ci()
    except AssertionError: checks['outside_ci_refused']=True
    else: raise AssertionError('Run this offline gate outside GitHub')
    workflow=(ROOT/'.github/workflows/proof-native.yml').read_text(encoding='utf-8')
    action_refs=re.findall(r'uses:\s*(actions/\S+)',workflow)
    assert len(action_refs)>=7 and all(re.fullmatch(r'actions/\S+@[0-9a-f]{40}',ref) for ref in action_refs)
    assert 'needs: linux-proof' in workflow and 'persist-credentials: false' in workflow
    checks['workflow_action_pins']=True
    write(ROOT/'validation/ci-results/package-check.json',dict(passed=True,checks=checks,sources=inputs(),
          scope='Offline package verification; no actual GitHub or Windows execution claimed'))
    print(json.dumps(checks,sort_keys=True))

if __name__=='__main__':main()
