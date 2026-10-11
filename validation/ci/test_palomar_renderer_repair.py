"""Regression coverage for the proposed dependency-merger exception."""

import argparse
import ast
from copy import deepcopy
import json
from pathlib import Path
import re
import sys
import unittest
from typing import Any
from urllib.parse import urlparse

from repair_palomar_renderer import apply_fix, PLAUSIBLE_REVISIONS

VERSO = '8fc7a297f14d5adc1a551b5b4ecf283c08bd691f'


def load_merger(pipeline, patched):
    namespace = {'re': re, 'Any': Any, 'Path': Path, 'urlparse': urlparse,
                 'VerificationError': RuntimeError, 'VERSO_REPOSITORY': 'leanprover/verso'}
    selected = []
    for file, names in [('submission_contract.py', {'GITHUB_RE', 'SHA_RE', 'LAKE_PACKAGE_NAME_RE',
                                                   'LAKE_ESCAPED_NAME_RE', 'lake_package_name'}),
                        ('verify_submission.py', {'github_repository'}),
                        ('render_challenge.py', {'manifest_package_key', 'merge_renderer_manifest'})]:
        code = (pipeline / 'scripts' / file).read_text(encoding='utf-8')
        if file == 'render_challenge.py' and patched:
            code = apply_fix(code)
        for node in ast.parse(code).body:
            if isinstance(node, ast.FunctionDef) and node.name in names:
                selected.append(node)
            elif isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id in names
                                                     for t in node.targets):
                selected.append(node)
    exec(compile(ast.Module(body=selected, type_ignores=[]), '<renderer-merger>', 'exec'), namespace)
    return namespace['merge_renderer_manifest']


class RepairRegression(unittest.TestCase):
    def setUp(self):
        self.project = json.loads(self.manifest.read_text())
        original = next(p for p in self.project['packages'] if p['name'] == 'plausible')
        # Reproduce the known conflict independently of the live project's pin.
        original['rev'] = original['inputRev'] = PLAUSIBLE_REVISIONS[0]
        alternative = deepcopy(original)
        alternative['rev'] = PLAUSIBLE_REVISIONS[1]
        self.verso = {'packages': [alternative]}

    def test_original_error_reproduced(self):
        with self.assertRaisesRegex(RuntimeError, "conflicts.*'plausible'"):
            self.original(self.project, self.verso, VERSO)

    def test_fix_retains_every_submitted_package_identity(self):
        merged = self.fixed(self.project, self.verso, VERSO)
        result = {p['name']: p for p in merged['packages']}
        for package in self.project['packages']:
            self.assertEqual(result[package['name']], package)

    def test_arbitrary_revision_is_rejected(self):
        self.verso['packages'][0]['rev'] = '0' * 40
        with self.assertRaises(RuntimeError):
            self.fixed(self.project, self.verso, VERSO)

    def test_fork_is_rejected(self):
        self.verso['packages'][0]['url'] = 'https://github.com/example/plausible'
        with self.assertRaises(RuntimeError):
            self.fixed(self.project, self.verso, VERSO)

    def test_other_package_name_is_rejected(self):
        other = deepcopy(self.project['packages'][0])
        other['name'] = 'other'
        self.project['packages'].append(other)
        alternative = deepcopy(other)
        alternative['rev'] = PLAUSIBLE_REVISIONS[1]
        self.verso = {'packages': [alternative]}
        with self.assertRaises(RuntimeError):
            self.fixed(self.project, self.verso, VERSO)

    def test_changed_configuration_or_subdir_is_rejected(self):
        for field, value in [('configFile', 'other.toml'), ('manifestFile', 'other.json'),
                             ('subDir', 'subproject')]:
            with self.subTest(field=field):
                alternative = deepcopy(self.verso)
                alternative['packages'][0][field] = value
                with self.assertRaises(RuntimeError):
                    self.fixed(self.project, alternative, VERSO)

    def test_invalid_git_revision_is_rejected(self):
        self.verso['packages'][0]['rev'] = 'not-a-commit'
        with self.assertRaises(RuntimeError):
            self.fixed(self.project, self.verso, VERSO)

    def test_non_git_package_is_rejected(self):
        self.verso['packages'][0] = {'name': 'plausible', 'type': 'path', 'dir': 'somewhere'}
        with self.assertRaises(RuntimeError):
            self.fixed(self.project, self.verso, VERSO)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pipeline', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    args = parser.parse_args()
    RepairRegression.manifest = args.manifest
    RepairRegression.original = staticmethod(load_merger(args.pipeline, False))
    RepairRegression.fixed = staticmethod(load_merger(args.pipeline, True))
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RepairRegression))
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(main())
