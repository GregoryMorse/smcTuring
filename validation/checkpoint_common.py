"""Portable strict source/axiom gate shared by published CI and errata checks."""
import hashlib, json, os, re
from pathlib import Path

ROOT = Path(os.environ.get('SMCTURING_SOURCE_ROOT', Path(__file__).resolve().parents[1])).resolve()

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()

def audit_gate():
    path = ROOT / 'validation/remote-evidence/lean.json'
    report = json.loads(path.read_text(encoding='utf-8'))
    assert report.get('passed') is True, 'Complete Linux audit is not passing'
    assert report['toolchain'] == 'leanprover/lean4:v4.35.0-rc3'
    assert report['commit'] == '470d5ce1400764999581fd26d5d72b00d990b0f4'
    current = {p.relative_to(ROOT).as_posix() for p in (ROOT/'lean').glob('*.lean')}
    current |= {p.relative_to(ROOT).as_posix() for p in (ROOT/'lean/SmcTuring').rglob('*.lean')}
    assert current == {n for n in report['sources'] if n.endswith('.lean')}, 'Audit source closure changed'
    for name, expected in report['sources'].items():
        assert digest(ROOT/name) == expected, 'Stale audit: ' + name
    assert digest(ROOT/'validation/remote-evidence/axiom-audit.log') == report['audit_sha256']
    expected = re.findall(r'^#print axioms (\S+)', (ROOT/'lean/Audit.lean').read_text(encoding='utf-8'), re.M)
    assert [d['name'] for d in report['declarations']] == expected and len(expected) == len(set(expected))
    assert all(set(d['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for d in report['declarations'])
    assert json.loads((ROOT/'validation/remote-evidence/resource.json').read_text(encoding='utf-8'))['exit'] == 0
    return dict(report_sha256=digest(path), declarations=len(expected), scope=report['scope'], overall_complete=False)
