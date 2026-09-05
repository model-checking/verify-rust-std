#!/usr/bin/env python3
"""Require specific positive and negative results from the experimental tool."""
from pathlib import Path
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit('usage: run.py /absolute/path/to/verifast')
base = Path(__file__).resolve().parent
verifier = Path(sys.argv[1]).resolve()
cases = [
    ('self-positive', True, '0 errors found'),
    ('self-free-negative', False, 'No such type parameter, inductive datatype, class, interface, or function type: Self'),
    ('alignment-positive', True, '0 errors found'),
    ('alignment-minimum-positive', True, '0 errors found'),
    ('alignment-wrong-negative', False, 'Cannot prove alignof(AlignedWide_type_info) = 1'),
    ('alignment-generic-negative', False, 'Cannot prove alignof(Generic_type_info(T_typeid)) = 8'),
    ('alignment-generic64-negative', False, 'Cannot prove alignof(Generic_type_info(WideAlignment_type_info)) = 8'),
    ('macro-second-negative', False, "Verifying function 'second_must_fail'"),
    ('own-sharing-usize', True, '0 errors found'),
    ('double-convert-negative', False, 'No matching heap chunks: points_to<u8>'),
    ('double-recover-negative', False, 'No matching heap chunks: borrow_end_token'),
]
failed = []
for name, success, diagnostic in cases:
    result = subprocess.run([str(verifier), '-skip_specless_fns', '-rustc_args',
                             '--edition=2024 --crate-type=lib', str(base / (name + '.rs'))],
                            capture_output=True, text=True)
    output = result.stdout + result.stderr
    (base / (name + '.log')).write_text(output)
    matches = (result.returncode == 0) == success and diagnostic in output
    print(f'{name}: {"PASS" if matches else "FAIL"} (exit {result.returncode})')
    if not matches:
        failed.append(name)
        print(output)
if failed:
    raise SystemExit('Unexpected result: ' + ', '.join(failed))
