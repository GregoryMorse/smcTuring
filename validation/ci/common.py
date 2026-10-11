"""Exact source identity shared by proof/native CI; no proof artifact exchange."""
import hashlib, json, os
from pathlib import Path

ROOT = Path(os.environ.get('SMCTURING_SOURCE_ROOT', Path(__file__).resolve().parents[2])).resolve()
VALIDATION = ROOT / 'validation'
CHAIN = 'leanprover/lean4:v4.35.0-rc3'
COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b''): h.update(chunk)
    return h.hexdigest()

def write(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')

def inputs():
    paths = set((ROOT/'lean').glob('*.lean'))
    paths.update((ROOT/'lean/SmcTuring').rglob('*.lean'))
    paths.update(ROOT/'lean'/x for x in ['lean-toolchain', 'lakefile.toml', 'lakefile.proof.toml', 'lake-manifest.json'])
    paths.update((ROOT/'validation').glob('*.py'))
    for suffix in ['*.cpp','*.asm','*.inc','*.h']:
        paths.update((ROOT/'validation').glob(suffix))
    paths.update((ROOT/'validation/ci').glob('*.py'))
    paths.update((ROOT/'validation/ci').glob('*.json'))
    paths.update(p for p in (ROOT/'validation/ci/reference').rglob('*') if p.is_file())
    paths.update((ROOT/'.github/workflows').glob('*.yml'))
    for directory in ['smcTuring', 'lean/errata']:
        paths.update(p for p in (ROOT/directory).rglob('*') if p.is_file()
                     and not any(x.startswith('.') or x in ['Debug','Release','x64','Win32'] for x in p.relative_to(ROOT/directory).parts))
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(paths)}

def verify_sources(sources):
    for name, expected in sources.items():
        assert digest(ROOT/name) == expected, 'Source mismatch: ' + name

def require_ci():
    assert os.environ.get('GITHUB_ACTIONS') == 'true', 'This installer/compiler is for isolated GitHub runners only'
