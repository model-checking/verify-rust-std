"""Require positive proof coverage and specific diagnostics for unsafe controls."""
from pathlib import Path
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent
if len(sys.argv) != 2:
    raise SystemExit('usage: run.py /absolute/path/to/experimental/verifast')
verifier = Path(sys.argv[1]).resolve()
subprocess.run([sys.executable, str(base / 'build-controls.py')], check=True)
cases = {
    'positive': (True, '0 errors found', 4),
    'ordering-matrix': (True, '0 errors found', 91),
    'type-domains': (True, '0 errors found', 17),
    'type-bool': (False, 'operand must be an integer', None),
    'type-float': (False, 'Floating point types are not yet supported', None),
    'type-tuple': (False, 'operand must be an integer', None),
    'type-fat-pointer': (False, 'operand must be an integer', None),
    'unsized-domain-rejected': (False, 'must implement trait Sized', None),
    'missing-domain': (False, 'Cannot prove std::intrinsics::atomic_type', None),
    'missing-resource': (False, 'No matching heap chunks: [_]std::intrinsics::atomic_points_to', None),
    'ordinary-resource': (False, 'No matching heap chunks: [_]std::intrinsics::atomic_points_to', None),
    'fractional-write': (False, 'No matching heap chunks: [_]std::intrinsics::atomic_points_to', None),
    'missing-closure': (False, 'No matching heap chunks: [_]std::intrinsics::is_atomic_rmw_preserves', None),
    'wrong-closure-op': (False, 'No matching heap chunks: [_]std::intrinsics::is_atomic_rmw_preserves', None),
    'wrong-closure-type': (False, 'No matching heap chunks: [_]std::intrinsics::is_atomic_rmw_preserves', None),
    'mismatched-integers': (False, 'RMW operands must be the same integer type', None),
    'pointer-update-type': (False, 'RMW operands must be the same integer type', None),
    'signed-max-unsigned': (False, 'signed min/max require a signed integer', None),
    'unsigned-min-signed': (False, 'unsigned min/max require an unsigned integer', None),
    'store-acquire': (False, 'Acquire and AcqRel are not permitted for stores', None),
    'store-acqrel': (False, 'Acquire and AcqRel are not permitted for stores', None),
    'load-release': (False, 'Release and AcqRel are not permitted for loads', None),
    'load-acqrel': (False, 'Release and AcqRel are not permitted for loads', None),
    'cxchg-failure-release': (False, 'Release and AcqRel are not permitted for compare-exchange failure', None),
    'cxchgweak-failure-acqrel': (False, 'Release and AcqRel are not permitted for compare-exchange failure', None),
    'invalid-bool-store': (False, 'Cannot prove', None),
    'invalid-bool-cxchg': (False, 'Cannot prove', None),
    'bool-nand-rejected': (False, 'Consuming function type postcondition', None),
    'bool-add-rejected': (False, 'Consuming function type postcondition', None),
}
results = []
for name, (success, diagnostic, expected_count) in cases.items():
    result = subprocess.run([str(verifier), '-verbose', '1', '-rustc_args',
                             '--edition=2024 --crate-type=lib', str(base / (name + '.rs'))],
                            capture_output=True, text=True)
    output = result.stdout + result.stderr
    functions = re.findall(r"Verifying function '([^']+)'", output)
    functions = [fn for fn in functions if not fn.startswith('std::') and fn != 'open_full_borrow_']
    # Ignore included standard ghost lemmas; require each real Rust function
    # declared in the concrete source to appear in the verification output.
    expected = set(re.findall(r'unsafe fn (\w+)', (base / (name + '.rs')).read_text()))
    coverage = expected <= set(functions)
    ok = (result.returncode == 0) == success and diagnostic in output
    if success:
        ok = ok and coverage and len(expected) == expected_count and 'arm64-apple-macosx (LP64)' in output
    lines = output.splitlines()
    saved = '\n'.join(line for line in lines if 'Verifying function ' in line or 'errors found' in line)
    if not success or not ok:
        saved = output
    (base / (name + '.log')).write_text(saved + '\n')
    results.append({'name': name, 'passed': ok, 'expected_success': success,
                    'exit': result.returncode, 'expected_diagnostic': diagnostic,
                    'rust_functions_covered': sorted(expected & set(functions))})
    print(f'{name}: {"PASS" if ok else "FAIL"} (exit {result.returncode})')
    if not ok:
        print('\n'.join(line for line in lines if 'error:' in line)[:2000])
(base / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
if not all(r['passed'] for r in results):
    raise SystemExit('Some controls did not produce the expected result.')
print(f'PASS: {len(results)} operation controls; 91 concrete orderings and all 17 operand-type witnesses covered.')
