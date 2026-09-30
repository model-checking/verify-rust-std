# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Collector integration test: stub external processes, exercise real packaging and hashes."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('collector', ROOT / 'scripts/collect-autoharness-dashboard.py')
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)


class FakeProcess:
    stdout = ['Kani generated automatic harnesses for 1 function(s):\n']

    def wait(self):
        return 0


class CollectorTest(unittest.TestCase):
    def test_capture_and_failure_propagation(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            work = root / 'work'
            work.mkdir()
            (work / 'tool_config').mkdir()
            (work / 'tool_config/kani-version.toml').write_text('[kani]\ncommit = "' + '1'*40 + '"\n')
            captured = []

            def fake_output(command, cwd):
                if command[:2] == ['git', 'status']:
                    return ''
                if command[0] == 'rustc':
                    return 'rustc fixture\nhost: x86_64-unknown-linux-gnu'
                return '1'*40

            def fake_run(command, **kwargs):
                captured.append(command)
                self.assertEqual(command[:4], ['scripts/run-kani.sh', '--run', 'metrics', '--with-autoharness'])
                self.assertEqual(command[-3:-1], ['--kani-args', '--target-dir'])
                self.assertNotIn('CARGO_TARGET_DIR', kwargs['env'])
                # Pinned std_project -> dummy crate; cargo_build_std does NOT
                # forward the target-dir flag as ordinary cargo_build does.
                target = Path(command[-1]) / 'kani_verify_std/target/x86_64-unknown-linux-gnu/debug/deps'
                target.mkdir(parents=True)
                (target / 'core-a.kani-metadata.json').write_text('{}')
                wrong_target = Path(command[-1]) / 'x86_64-unknown-linux-gnu/debug/deps'
                wrong_target.mkdir(parents=True)
                (wrong_target / 'stale.kani-metadata.json').write_text('{"stale":true}')
                (work / 'kani-list.json').write_text('{"kani-version":"fixture"}')
                (work / 'kani_build').mkdir(exist_ok=True)
                (work / 'kani_build/rust-toolchain.toml').write_text('[toolchain]\nchannel="fixture"')
                metrics = work / 'scripts/kani-std-analysis'
                metrics.mkdir(parents=True, exist_ok=True)
                for crate in ['core', 'alloc', 'std']:
                    (metrics / f'metrics-data-{crate}.json').write_text('{"results":[]}')
                return FakeProcess()

            dest = root / 'raw'
            argv = ['collector', '--work-dir', str(work), '--output-dir', str(dest)]
            with patch('sys.argv', argv), patch.object(collector.platform, 'system', return_value='Linux'), patch.object(collector.platform, 'machine', return_value='x86_64'), patch.object(collector, 'output', side_effect=fake_output), patch.object(collector.subprocess, 'Popen', side_effect=fake_run), patch.dict('os.environ', {'GITHUB_ACTIONS':'false','CARGO_TARGET_DIR':'must-not-use'}), contextlib.redirect_stdout(io.StringIO()):
                collector.main()
                with self.assertRaises(FileExistsError):
                    collector.main()
            run = json.loads((dest / 'run.json').read_text())
            self.assertEqual(len(captured), 1)
            self.assertEqual(run['kaniCommit'], run['expectedKaniCommit'])
            self.assertFalse(Path(captured[0][-1]).exists())
            self.assertEqual([p.name for p in (dest / 'metadata').iterdir()], ['core-a.kani-metadata.json'])
            for entry in run['files']:
                self.assertEqual(entry['sha256'], hashlib.sha256((dest / entry['path']).read_bytes()).hexdigest())
            ci_dest = root / 'fork-run'
            ci_env = {'GITHUB_ACTIONS':'true', 'GITHUB_SERVER_URL':'https://github.com',
                      'GITHUB_REPOSITORY':'example/verify-rust-std', 'GITHUB_WORKFLOW':'Kani Metrics Update',
                      'GITHUB_RUN_ID':'123', 'GITHUB_RUN_ATTEMPT':'2'}
            with patch('sys.argv', ['collector','--work-dir',str(work),'--output-dir',str(ci_dest)]), patch.object(collector.platform,'system',return_value='Linux'), patch.object(collector.platform,'machine',return_value='x86_64'), patch.object(collector,'output',side_effect=fake_output), patch.object(collector.subprocess,'Popen',side_effect=fake_run), patch.dict('os.environ',ci_env), contextlib.redirect_stdout(io.StringIO()):
                collector.main()
            ci_run = json.loads((ci_dest / 'run.json').read_text())
            self.assertEqual(ci_run['repository'], 'https://github.com/example/verify-rust-std')
            self.assertEqual(ci_run['workflow']['url'], 'https://github.com/example/verify-rust-std/actions/runs/123')
            self.assertEqual(ci_run['workflow']['attempt'], '2')
            failed = root / 'failed'
            with patch('sys.argv', ['collector','--work-dir',str(work),'--output-dir',str(failed)]), patch.object(collector.platform,'system',return_value='Linux'), patch.object(collector.platform,'machine',return_value='x86_64'), patch.object(collector,'output',side_effect=fake_output), patch.object(collector.subprocess,'Popen',return_value=FakeProcess()), patch.object(FakeProcess,'wait',return_value=1), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(RuntimeError, 'metrics failed'):
                    collector.main()
            self.assertTrue((failed / 'metrics.log').exists())
            self.assertFalse((failed / 'run.json').exists())


if __name__ == '__main__':
    unittest.main()
