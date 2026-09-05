#!/usr/bin/env python3
"""Check source identity, all from_ptr and generic wrapper proofs, and refinement."""
from pathlib import Path
import json
import re
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'checks/operations'))
from annotate import OPS

if len(sys.argv) != 2:
    raise SystemExit('usage: run.py /absolute/path/to/experimental-runtime/bin')
base = Path(__file__).resolve().parent
runtime = Path(sys.argv[1]).resolve()
subprocess.run([sys.executable, str(base / 'generate.py')], check=True)
expected = {'atomic::AtomicBool::from_ptr', 'atomic::AtomicPtr::<T>::from_ptr'}
expected.update('atomic::Atomic' + kind + '::from_ptr'
                for kind in ('I8','U8','I16','U16','I32','U32','I64','U64','I128','U128','Isize','Usize'))
expected_wrappers = {'atomic::atomic_' + op for op in OPS}
args = '--edition=2024 --crate-type=lib'
command = [str(runtime / 'verifast'), '-verbose', '1', '-skip_specless_fns',
           '-rustc_args', args, str(base / 'verified/lib.rs')]
result = subprocess.run(command, capture_output=True, text=True)
output = result.stdout + result.stderr
verified = set(re.findall(r"Verifying function '([^']+::from_ptr)'", output))
wrappers = set(re.findall(r"Verifying function '(atomic::atomic_[^']+)'", output))
target_match = re.search(r'target: (.*)\)', output)
target = target_match.group(1) if target_match else None
(base / 'proof.log').write_text('\n'.join(line for line in output.splitlines()
    if 'Verifying function ' in line or 'errors found' in line or 'error:' in line) + '\n')
if result.returncode != 0 or '0 errors found' not in output or verified != expected or wrappers != expected_wrappers or target != 'arm64-apple-macosx (LP64)':
    (base / 'failure.log').write_text(output)
    raise SystemExit(f'Proof/coverage failed: exit={result.returncode}, missing={sorted((expected-verified) | (expected_wrappers-wrappers))}, extra={sorted((verified-expected) | (wrappers-expected_wrappers))}')
command = [str(runtime / 'refinement-checker'), '--verbose', '0', '--rustc-args', args,
           str(base / 'normalized-original/lib.rs'), str(base / 'verified/lib.rs')]
result = subprocess.run(command, capture_output=True, text=True)
output = result.stdout + result.stderr
(base / 'refinement.log').write_text(output)
if result.returncode != 0 or 'No refinement errors found' not in output:
    raise SystemExit('Refinement failed; see refinement.log')
expected_clients = {'clients::alias_' + name for name in ('bool','ptr','i8','u8','i16','u16','i32','u32','i64','u64','i128','u128','isize','usize')}
result = subprocess.run([str(runtime / 'verifast'), '-verbose','1','-skip_specless_fns',
                         '-rustc_args',args,str(base / 'clients-lib.rs')], capture_output=True, text=True)
output = result.stdout + result.stderr
clients = set(re.findall(r"Verifying function '(clients::alias_[^']+)'", output))
(base / 'clients.log').write_text('\n'.join(line for line in output.splitlines() if 'Verifying function ' in line or 'errors found' in line or 'error:' in line) + '\n')
if result.returncode != 0 or '0 errors found' not in output or clients != expected_clients:
    (base / 'failure.log').write_text(output)
    raise SystemExit('Fresh/shared caller coverage failed')
client_controls = {}
for name, diagnostic in [('double-fresh','No matching heap chunks: points_to<bool>'),
                         ('shared-without-permission','No matching heap chunks: [_]atomic::AtomicBool_share'),
                         ('uninitialized','No matching heap chunks: points_to<bool>')]:
    result = subprocess.run([str(runtime / 'verifast'), '-skip_specless_fns', '-rustc_args',args,
                             str(base / f'clients-{name}-lib.rs')], capture_output=True, text=True)
    output = result.stdout + result.stderr
    (base / f'clients-{name}.log').write_text(output)
    client_controls[name] = result.returncode != 0 and diagnostic in output
    if not client_controls[name]:
        raise SystemExit(f'Unexpected {name} control: ' + output)
(base / 'coverage.json').write_text(json.dumps({
    'runtime': str(runtime), 'approved_release': False,
    'rust_edition': 2024, 'target': target,
    'source_identity_checked': True,
    'source_normalization': 'rustc_diagnostic_item attributes changed to doc attributes in both proof inputs',
    'from_ptr_functions_verified': sorted(verified),
    'generic_operation_wrappers_verified': sorted(wrappers),
    'panic_paths_verified': True,
    'allow_dead_code': False,
    'fresh_and_shared_callers_verified': sorted(clients),
    'from_ptr_negative_controls': client_controls,
    'refinement_passed': True,
    'remaining': ['independent model and source-boundary review', 'acceptance of tool patch and source preparation', 'CI integration'],
}, indent=2) + '\n')
print(f'PASS: exact source copy, all {len(verified)} from_ptr bodies, all {len(wrappers)} generic operation wrappers, panic paths, {len(clients)} fresh/shared callers, 3 negative controls, and whole-module refinement after documented metadata normalization.')
