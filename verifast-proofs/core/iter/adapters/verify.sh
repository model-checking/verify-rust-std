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
ulimit -v 2097152
ulimit -t 600
export VFVERSION=25.11
export CARGO_BUILD_JOBS=1
export RAYON_NUM_THREADS=1
export PATH="$proof_dir/../../..:$PATH"

# Keep every stage sequential and fail on any unsuccessful proof or refinement.
# No assumption, unwind, reference-creation, or overflow suppression flags.
timeout --signal=TERM --kill-after=10s 600s \
  verifast -rustc_args '--edition 2024' -skip_specless_fns verified/lib.rs
timeout --signal=TERM --kill-after=10s 600s \
  refinement-checker --rustc-args '--edition 2024' original/lib.rs verified/lib.rs
python3 -I check_sources.py
echo 'PASS: generic adapter contracts, source refinement, and source identity'
