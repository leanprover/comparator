#!/usr/bin/env python3
"""Exercise result JSON on real trusted fixtures; sandbox qualification is separate."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / '.lake/build/bin/comparator'


def invoke(project, *args):
    return subprocess.run(['lake', 'env', str(BIN), *args], cwd=project,
                          capture_output=True, text=True, timeout=120)


def fixture(root, name, folder=None):
    project = root / (folder or name)
    shutil.copytree(ROOT / 'tests/projects' / name, project)
    shutil.copyfile(ROOT / 'lean-toolchain', project / 'lean-toolchain')
    if not (project / 'lakefile.toml').exists():
        (project / 'lakefile.toml').write_text(
            'name = "resulttest"\n[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Solution"\n')
    return project


def check(project, result, outcome, stage, reason):
    proc = invoke(project, 'config.json', '--result-json', str(result))
    data = json.loads(result.read_text())
    assert data['schemaVersion'] == 1, data
    assert (data['outcome'], data['stage'], data['reason']) == (outcome, stage, reason), data
    assert (proc.returncode == 0) == (outcome == 'pass'), proc.stdout + proc.stderr
    assert data['leanVersion'], data
    return data


def main():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        for name, outcome, stage, reason in (
            ('simple_match', 'pass', 'complete', 'verified'),
            ('simple_mismatch', 'rejected', 'target_comparison', 'target_mismatch'),
            ('simple_axiom_issue', 'rejected', 'axiom_policy', 'disallowed_axiom'),
            ('def_hole_axiom_issue', 'rejected', 'axiom_policy', 'disallowed_axiom'),
        ):
            project = fixture(root, name)
            result = root / (name + '.json')
            data = check(project, result, outcome, stage, reason)
            assert data['config']['theorem_names'] == json.loads((project / 'config.json').read_text())['theorem_names']
            assert (invoke(project, 'config.json').returncode == 0) == (outcome == 'pass')
            before = result.read_bytes()
            assert invoke(project, 'config.json', '--result-json', str(result)).returncode != 0
            assert result.read_bytes() == before
            print('PASS', name, flush=True)
        project = fixture(root, 'simple_match', 'bad_config')
        (project / 'config.json').write_text('{')
        check(project, root / 'bad_config.json', 'error', 'configuration', 'execution_error')
        project = fixture(root, 'simple_match', 'bad_build')
        (project / 'Solution.lean').write_text('this cannot elaborate\n')
        check(project, root / 'bad_build.json', 'error', 'solution_build', 'execution_error')
        project = fixture(root, 'simple_match', 'external_error')
        config = json.loads((project / 'config.json').read_text())
        config['external_kernels'] = {'crashing_kernel': ['/bin/false']}
        (project / 'config.json').write_text(json.dumps(config))
        check(project, root / 'external_error.json', 'error', 'external_kernels', 'execution_error')
        print('PASS configuration, build and external-process errors; no log classification')


if __name__ == '__main__':
    main()
