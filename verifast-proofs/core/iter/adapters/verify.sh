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

# Keep every stage sequential and fail on any unsuccessful proof or refinement.
# No assumption, unwind, reference-creation, or overflow suppression flags.
timeout --signal=TERM --kill-after=10s 600s \
  verifast -rustc_args '--edition 2024' -skip_specless_fns verified/lib.rs
timeout --signal=TERM --kill-after=10s 600s \
  refinement-checker --rustc-args '--edition 2024' original/lib.rs verified/lib.rs
python3 -I check_sources.py
echo 'PASS: generic adapter contracts, source refinement, and source identity'
