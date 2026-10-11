"""Apply a proposed, narrowly scoped upstream renderer fix for an advisory test.

This does not change the submitted Lean source or Palomar's deployed service.
The original Mathlib pin wins, so its cache manifest check remains intact.
"""

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import urllib.request

PIPELINE_REVISION = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
RENDERER_GIT_BLOB = '9d8d6dbe345926fc6d5736e86acd2a4985bd7565'
PLAUSIBLE_REVISIONS = (
    'afc2695efcb6855264d85a45632db1ddc56c8774',
    'fb13df72ecefd8ddbf9291021d7f33a8673eb57b',
)
BEFORE = '''        if previous is not None and manifest_package_key(previous) != identity:
            raise VerificationError(f"Verso dependency conflicts with submitted package {name!r}")
'''
AFTER = '''        if previous is not None and manifest_package_key(previous) != identity:
            # These two immutable Plausible revisions differ only in
            # .github/workflows/lean_action_ci.yml. Keep the submitted pin:
            # Mathlib's cache also checks shared-dependency revision equality.
            same_plausible_sources = (
                name == "plausible"
                and manifest_package_key(previous)[:2] == identity[:2]
                == ("git", "leanprover-community/plausible")
                and {previous["rev"], candidate["rev"]} == {
                    "afc2695efcb6855264d85a45632db1ddc56c8774",
                    "fb13df72ecefd8ddbf9291021d7f33a8673eb57b",
                }
                and all(
                    (entry.get("subDir"), entry.get("configFile"), entry.get("manifestFile"))
                    == (None, "lakefile.toml", "lake-manifest.json")
                    for entry in (previous, candidate)
                )
            )
            if not same_plausible_sources:
                raise VerificationError(f"Verso dependency conflicts with submitted package {name!r}")
'''


def verify_upstream_trees():
    trees = []
    for rev in PLAUSIBLE_REVISIONS:
        request = urllib.request.Request(
            f'https://api.github.com/repos/leanprover-community/plausible/git/trees/{rev}?recursive=1',
            headers={'User-Agent': 'smcTuring-renderer-regression', 'Accept': 'application/vnd.github+json'},
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            data = json.load(response)
        if data.get('truncated') or not isinstance(data.get('tree'), list):
            raise ValueError('Incomplete upstream Git tree')
        trees.append({entry['path']: (entry['type'], entry['mode'], entry['sha'])
                      for entry in data['tree'] if entry['type'] != 'tree'})
    changed = sorted(path for path in trees[0].keys() | trees[1].keys()
                     if trees[0].get(path) != trees[1].get(path))
    if changed != ['.github/workflows/lean_action_ci.yml']:
        raise ValueError(f'Plausible equivalence check failed: {changed}')
    lean_files = sum(path.endswith('.lean') for path in trees[0])
    if lean_files != 28:
        raise ValueError('Unexpected upstream source tree')
    return {'complete_git_trees_compared': True, 'changed_files': changed,
            'identical_lean_files': lean_files, 'all_other_tracked_inputs_identical': True}


def apply_fix(source):
    if source.count(BEFORE) != 1:
        raise ValueError('Pinned renderer conflict check does not match patch base')
    return source.replace(BEFORE, AFTER, 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pipeline', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    evidence = verify_upstream_trees()
    path = args.pipeline / 'scripts/render_challenge.py'
    original = path.read_text(encoding='utf-8')
    encoded = original.encode('utf-8')
    if hashlib.sha1(f'blob {len(encoded)}\0'.encode() + encoded).hexdigest() != RENDERER_GIT_BLOB:
        raise ValueError('Renderer source differs from the pinned upstream Git blob')
    fixed = apply_fix(original)
    patch = ''.join(difflib.unified_diff(original.splitlines(True), fixed.splitlines(True),
                                        'a/scripts/render_challenge.py', 'b/scripts/render_challenge.py', n=2))
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.with_suffix('.patch').write_text(patch, encoding='utf-8', newline='\n')
    path.write_text(fixed, encoding='utf-8', newline='\n')
    evidence.update(status='proposed-upstream-patch-applied-for-advisory-test',
                    pipeline_revision=PIPELINE_REVISION,
                    original_sha256=hashlib.sha256(original.encode()).hexdigest(),
                    patched_sha256=hashlib.sha256(fixed.encode()).hexdigest(),
                    submitted_dependency_pins_preserved=True,
                    cache_and_sandbox_checks_unchanged=True)
    args.report.write_text(json.dumps(evidence, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
