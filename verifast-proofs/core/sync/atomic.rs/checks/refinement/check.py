#!/usr/bin/env python3
"""Run the isolated AtomicOrdering refinement checks against a supplied checker."""
from pathlib import Path
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: python3 rc-run.py /absolute/path/to/refinement-checker")

base = Path(__file__).resolve().parent
checker = Path(sys.argv[1]).resolve()
cases = [
    ("rc-positive", "rc-original", "rc-positive", True,
     ["No refinement errors found", "checking refinement"]),
    ("rc-wrong-order", "rc-original", "rc-wrong-order", False,
     ["The constants", "are not equal", "AtomicOrdering::Relaxed", "AtomicOrdering::SeqCst"]),
    ("rc-other-enum", "rc-other-original", "rc-other-verified", False,
     ["Branch not supported (expected a fieldless AtomicOrdering constant)"]),
    ("rc-integer", "rc-integer-original", "rc-integer-verified", True,
     ["No refinement errors found", "checking refinement"]),
]
failures = []
for label, original, verified, should_pass, evidence in cases:
    command = [str(checker), "--verbose", "0", str(base / original / "lib.rs"),
               str(base / verified / "lib.rs")]
    result = subprocess.run(command, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (base / (label + "-local-patched26.01-checker.log")).write_text(
        f"Tool: {checker}\nProvenance: local modified VeriFast 26.01, not the approved release binary\n\n" + output)
    accepted = (result.returncode == 0) == should_pass and all(s in output for s in evidence)
    print(f"{label}: {'PASS' if accepted else 'FAIL'} (checker exit {result.returncode})")
    if not accepted:
        failures.append(label)
        print(output)
if failures:
    raise SystemExit("Unexpected result: " + ", ".join(failures))
