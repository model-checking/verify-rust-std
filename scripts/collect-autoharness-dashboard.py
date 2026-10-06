#!/usr/bin/env python3
# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Run metrics once and capture a self-contained, checksummed dashboard input bundle."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import platform
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib


def output(command, cwd):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def now():
    return datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--repository', default=None,
                        help='Source repository URL for local runs (CI uses GITHUB_REPOSITORY)')
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error(
            "official collection runs on the GitHub Actions Linux x86_64 runner; "
            "on macOS, download a raw CI artifact and run the dashboard importer instead"
        )
    work, dest = args.work_dir.resolve(), args.output_dir.resolve()
    # Never merge with old output, even after an interrupted run.
    dest.mkdir(parents=True, exist_ok=False)
    started = now()
    pin = tomllib.loads((work / 'tool_config/kani-version.toml').read_text())['kani']['commit']
    source_sha = output(['git', 'rev-parse', 'HEAD'], work)
    library_tree = output(['git', 'rev-parse', 'HEAD:library'], work)
    if output(['git', 'status', '--porcelain', '--untracked-files=normal', '--', 'library', 'tool_config/kani-version.toml', 'scripts/run-kani.sh', 'scripts/kani-std-analysis'], work):
        raise RuntimeError('Commit analysis inputs before collecting official provenance')
    with tempfile.TemporaryDirectory(prefix='autoharness-dashboard-') as target:
        command = ['scripts/run-kani.sh', '--run', 'metrics', '--with-autoharness',
                   '--path', str(work), '--kani-args', '--target-dir', target]
        env = os.environ.copy()
        for name in ['KANI_TOML_FILE', 'KANI_REPO_URL', 'KANI_BRANCH_NAME', 'CARGO_TARGET_DIR', 'CARGO_BUILD_TARGET']:
            env.pop(name, None)
        # Explicitly propagate failures through the subprocess; no shell tee pipeline.
        with (dest / 'metrics.log').open('w') as log:
            result = subprocess.Popen(command, cwd=work, env=env, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, text=True)
            for line in result.stdout:
                log.write(line)
                print(line, end='', flush=True)
            if result.wait() != 0:
                raise RuntimeError('Kani metrics failed; see metrics.log')
        kani = work / 'kani_build'
        actual_pin = output(['git', 'rev-parse', 'HEAD'], kani)
        if actual_pin != pin:
            raise RuntimeError('Built Kani SHA does not match configured pin')
        rustc = output(['rustc', '-Vv'], kani)
        host = next(line.removeprefix('host: ') for line in rustc.splitlines() if line.startswith('host: '))
        if host != 'x86_64-unknown-linux-gnu':
            raise RuntimeError(f'Official dashboard collection requires x86_64-unknown-linux-gnu, got {host}')
        # Pinned Kani 152c6a8: std_project creates <target>/kani_verify_std;
        # cargo_build_std runs Cargo there WITHOUT forwarding --target-dir.
        # This differs from Kani's ordinary cargo_build implementation.
        deps = Path(target) / 'kani_verify_std' / 'target' / host / 'debug' / 'deps'
        metadata = sorted(deps.glob('*.kani-metadata.json'))
        if not metadata:
            raise RuntimeError(f'No metadata in this run target directory: {deps}')
        for folder in ['metadata', 'scanner', 'metrics']:
            (dest / folder).mkdir()
        # Keep dummy/build-scaffolding metadata: the Kani listing includes emitted crates.
        # The importer excludes only KaniImpl and checks the terminal totals.
        for path in metadata:
            shutil.copy2(path, dest / 'metadata' / path.name)
        shutil.copy2(work / 'kani-list.json', dest / 'kani-list.json')
        for path in Path('/tmp/std_lib_analysis/results').glob('*.csv'):
            shutil.copy2(path, dest / 'scanner' / path.name)
        for crate in ['core', 'alloc', 'std']:
            name = f'metrics-data-{crate}.json'
            shutil.copy2(work / 'scripts/kani-std-analysis' / name, dest / 'metrics' / name)
        listing = json.loads((dest / 'kani-list.json').read_text())
        workflow = None
        repository = args.repository or 'https://github.com/model-checking/verify-rust-std'
        if env.get('GITHUB_ACTIONS') == 'true':
            repository = f"{env['GITHUB_SERVER_URL']}/{env['GITHUB_REPOSITORY']}"
            workflow = {'name': env['GITHUB_WORKFLOW'], 'runId': env['GITHUB_RUN_ID'],
                        'attempt': env['GITHUB_RUN_ATTEMPT'],
                        'url': f"{env['GITHUB_SERVER_URL']}/{env['GITHUB_REPOSITORY']}/actions/runs/{env['GITHUB_RUN_ID']}"}
        manifest = {
            'schemaVersion': 1, 'runId': f"{source_sha}:{started}",
            'repository': repository,
            'verifyRustStdCommit': source_sha, 'libraryTree': library_tree,
            'expectedKaniCommit': pin, 'kaniCommit': actual_pin,
            'kaniVersion': listing['kani-version'], 'target': host, 'host': host,
            'rustcVersion': rustc, 'toolchain': (kani / 'rust-toolchain.toml').read_text(),
            'startedAt': started, 'completedAt': now(), 'workflow': workflow,
            # Portable representation; literal ephemeral paths are not meaningful provenance.
            'command': ['scripts/run-kani.sh', '--run', 'metrics', '--with-autoharness',
                        '--path', '<checkout>', '--kani-args', '--target-dir', '<isolated-run-target>'],
            'scannerSource': 'Kani toolchain rust-src, not the verify-rust-std library snapshot',
            'files': [{'path': path.relative_to(dest).as_posix(),
                       'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                      for path in sorted(dest.rglob('*')) if path.is_file()],
        }
        (dest / 'run.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
