#!/usr/bin/env bash
set -euo pipefail

proof_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$proof_dir"

case "${1:-}" in
  --static)
    exec python3 -I check_sources.py
    ;;
  --remote)
    ;;
  *)
    echo 'Usage: bash verify.sh --static | --remote' >&2
    echo '--remote runs compilers and solvers on a prepared Linux machine.' >&2
    exit 2
    ;;
esac

# Do not invoke the repository wrappers on the memory-constrained Mac.
# The wrappers may install VeriFast and its pinned Rust toolchain.
if [[ "$(uname -s)" != Linux ]]; then
  echo 'Proof execution requires a separate Linux machine. Use --static here.' >&2
  exit 2
fi

python3 -I check_sources.py

# This is a per-process address-space limit, not an aggregate process-tree cap.
# Require headroom for the verifier, Rust frontend, solver, and operating system.
python3 -I - <<'PY'
from pathlib import Path
import sys

fields = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
available_kib = int(fields["MemAvailable"].split()[0])
if available_kib < 8 * 1024 * 1024:
    sys.exit("Proof execution requires at least 8 GiB currently available RAM.")
print(f"Remote preflight: {available_kib // 1024} MiB available RAM")
PY

command -v timeout >/dev/null
ulimit -c 0
ulimit -t 600
export VFVERSION=26.09
export CARGO_BUILD_JOBS=1
export RAYON_NUM_THREADS=1
export PATH="$proof_dir/../../..:$PATH"

# Install the pinned release and build its patched Rust frontend remotely.
# The workflow's cgroup also covers this build. Proof processes get the tighter
# per-process address-space limit after the compiler has finished.
export VFPLATFORM=linux
# shellcheck source=/dev/null
source "$proof_dir/../../../setup-verifast-home"
export VERIFAST_HOME
timeout --signal=TERM --kill-after=10s 900s bash backend/prepare.sh --remote
ulimit -v 2097152

# Check both the defined-input case and rejection of a potentially overflowing
# input before trusting the frontend mapping for the adapter proof.
timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/add-valid.rs
timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/const-valid.rs
if ! timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/array-valid.rs; then
  # The regression already failed. Emit heap context without changing that verdict.
  diagnostic_status=0
  timeout --signal=TERM --kill-after=5s 30s \
    verifast -json -rustc_args '--edition 2024' backend/array-valid.rs || diagnostic_status=$?
  printf 'Array regression diagnostic status: %s\n' "$diagnostic_status"
  exit 1
fi
negative_log="$(mktemp)"
trap 'rm -f -- "$negative_log"' EXIT
if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/add-overflow.rs >"$negative_log" 2>&1; then
  cat "$negative_log"
  echo 'The frontend accepted unchecked addition without an overflow precondition.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "Potential arithmetic overflow." not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The negative check did not produce the required overflow diagnostic.")
PY
if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/const-invalid.rs >"$negative_log" 2>&1; then
  cat "$negative_log"
  echo 'The frontend accepted an incorrect symbolic array length.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "Cannot prove" not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The const-parameter negative check did not reach a proof failure.")
PY
if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/array-invalid.rs >"$negative_log" 2>&1; then
  cat "$negative_log"
  echo 'The frontend accepted an array reference without a shared borrow.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "No matching heap chunks" not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The array-reference negative check did not reach a borrow proof failure.")
PY
if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/array-mut-invalid.rs >"$negative_log" 2>&1; then
  cat "$negative_log"
  echo 'The frontend accepted a mutable array reference without owning its storage.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "No matching heap chunks" not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The mutable-array negative check did not reach a storage proof failure.")
PY
timeout --signal=TERM --kill-after=10s 60s \
  refinement-checker --rustc-args '--edition 2024' \
  backend/refinement-original.rs backend/refinement-valid.rs
if timeout --signal=TERM --kill-after=10s 60s \
  refinement-checker --rustc-args '--edition 2024' \
  backend/refinement-original.rs backend/refinement-invalid.rs >"$negative_log" 2>&1; then
  cat "$negative_log"
  echo 'The refinement checker equated distinct symbolic const parameters.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if not all(s in diagnostics for s in ("ConstParamTerm N", "ConstParamTerm M", "not equal")):
    sys.exit("The refinement negative check did not distinguish the two const parameters.")
PY

if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/matrix-invalid.rs >"$negative_log" 2>&1; then
  echo 'The array-to-slice negative check unexpectedly passed.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "No matching heap chunks" not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The array-to-slice negative check did not reject missing reference permissions.")
PY

timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/nonzero-valid.rs
if timeout --signal=TERM --kill-after=10s 60s \
  verifast -rustc_args '--edition 2024' backend/nonzero-invalid.rs >"$negative_log" 2>&1; then
  echo 'The NonZero negative check unexpectedly passed.' >&2
  exit 1
fi
cat "$negative_log"
python3 -I - "$negative_log" <<'PY'
from pathlib import Path
import sys

diagnostics = Path(sys.argv[1]).read_text()
if "Cannot prove" not in diagnostics or "Rust frontend failed" in diagnostics:
    sys.exit("The NonZero negative check did not reject the missing nonzero precondition.")
PY

# Keep every stage sequential and require both proof and refinement to succeed.
# Collect their independent diagnostics even when the first stage fails.
# No assumption, unwind, reference-creation, or overflow suppression flags.
proof_status=0
timeout --signal=TERM --kill-after=10s 600s \
  verifast -rustc_args '--edition 2024' -skip_specless_fns verified/lib.rs || proof_status=$?
refinement_status=0
timeout --signal=TERM --kill-after=10s 600s \
  refinement-checker --rustc-args '--edition 2024' original/lib.rs verified/lib.rs || refinement_status=$?
python3 -I check_sources.py
if (( proof_status != 0 )); then
  # These bounded, sequential diagnostics cannot replace the full proof verdict.
  while IFS= read -r proof_location; do
    diagnostic_status=0
    timeout --signal=TERM --kill-after=5s 30s \
      verifast -rustc_args '--edition 2024' -skip_specless_fns \
      -focus "$proof_location" verified/lib.rs || diagnostic_status=$?
    printf 'Diagnostic %s: status %s\n' "$proof_location" "$diagnostic_status"
  done < <(python3 -I - <<'PY'
from pathlib import Path
import re

for path in (Path("verified/map_windows.rs"), Path("verified/step_by.rs")):
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if re.match(r"\s*(?:unsafe\s+)?fn\s+\w+", line):
            print(f"{path}:{line_number}")
PY
  )
fi
if (( proof_status != 0 || refinement_status != 0 )); then
  printf 'FAIL: proof status %s; refinement status %s\n' "$proof_status" "$refinement_status" >&2
  exit 1
fi
echo 'PASS: generic adapter contracts, source refinement, and source identity'
