#!/usr/bin/env python3
"""Run every safety, source-connection, and negative-control gate for atomics."""
from pathlib import Path
import json
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit('usage: check.py /absolute/path/to/experimental-runtime/bin')
base = Path(__file__).resolve().parent
runtime = Path(sys.argv[1]).resolve()
checks = [
    ('source and fresh/shared callers', base / 'proof/check.py', runtime),
    ('compiler/layout/ownership controls', base / 'checks/source/check.py', runtime / 'verifast'),
    ('intrinsic types, orderings, and invariants', base / 'checks/operations/run.py', runtime / 'verifast'),
    ('ordering refinement controls', base / 'checks/refinement/check.py', runtime / 'refinement-checker'),
]
for name, script, argument in checks:
    print('Checking ' + name, flush=True)
    subprocess.run([sys.executable, str(script), str(argument)], check=True)
provenance = json.loads((base / 'toolchain/provenance.json').read_text())
schema = runtime.parent.parent / provenance['source_archive_prefix'] / 'src/rust_frontend/vf_mir/vf_mir.capnp'
print('Checking malformed MIR with an isolated replay exporter', flush=True)
subprocess.run([sys.executable, str(base / 'checks/decoder/check.py'), str(runtime), str(schema)], check=True)
coverage = json.loads((base / 'proof/coverage.json').read_text())
operations = json.loads((base / 'checks/operations/results.json').read_text())
assert len(coverage['from_ptr_functions_verified']) == 14
assert len(coverage['generic_operation_wrappers_verified']) == 15
assert len(coverage['fresh_and_shared_callers_verified']) == 14
assert all(coverage['from_ptr_negative_controls'].values())
assert len(operations) == 29 and all(result['passed'] for result in operations)
print('PASS: complete required atomic proof scope and all configured rejection controls.', flush=True)
